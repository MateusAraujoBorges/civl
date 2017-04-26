package edu.udel.cis.vsl.civl.library.civlc;

import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.CoreUniverse.ForallStructure;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericSymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject.SymbolicObjectKind;

/**
 * This class provides APIs to transform and reason the validity of a boolean
 * expression e with heuristics when the validity of e was unknown.
 * 
 * @author ziqing
 */
public class HeuristicProveHelper {

	/**
	 * Reasoning the given predicate with application of heuristic
	 * transformations. Returns newly reasoned {@link ResultType} if any change
	 * happens due to the transformation, otherwise returns MAYBE.
	 * 
	 * @param reasoner
	 *            A reference to a {@link Reasoner}
	 * @param universe
	 *            A reference to a {@link SymbolicUniverse}
	 * @param predicate
	 *            The predicate will be reasoned
	 * @return The {@link ResultType} of the reason of transformed predicate.
	 *         {@link ResultType#MAYBE} if nothing changes.
	 */
	static ResultType applyHeuristics(Reasoner reasoner,
			SymbolicUniverse universe, BooleanExpression predicate) {
		Map<SymbolicExpression, SymbolicExpression> subMap = null;
		BooleanExpression newPredicate = predicate;

		// Universal quantification heuristics:
		for (BooleanExpression forall : universalQuantifiedExpressionsIn(
				predicate)) {
			ForallStructure structure = universe.getForallStructure(forall);
			Pair<BooleanExpression, BooleanExpression> forallExp = null;

			if (structure == null)
				continue;
			forallExp = universalQuantifiedOneWayExpansion(reasoner, universe,
					forall, structure);
			if (forallExp == null)
				continue;
			if (reasoner.isValid(forallExp.left))
				if (reasoner.isValid(forallExp.right)) {
					if (subMap == null)
						subMap = new TreeMap<>(universe.comparator());
					subMap.put(structure.body, universe.trueExpression());
				}
		}
		if (subMap != null) {
			ResultType resultType;

			newPredicate = (BooleanExpression) universe.mapSubstituter(subMap)
					.apply(predicate);
			subMap.clear();
			resultType = reasoner.valid(newPredicate).getResultType();
			if (resultType != ResultType.MAYBE)
				return resultType;
		}

		// summation heuristics:
		for (SymbolicExpression sigma : summationsInExpression(universe,
				newPredicate)) {
			SymbolicExpression sigmaExp = summationOneWayExpansion(reasoner,
					universe, sigma);

			if (sigmaExp == null)
				continue;
			if (subMap == null) {
				subMap = new TreeMap<>(universe.comparator());
				subMap.put(sigma, sigmaExp);
			}
		}
		if (subMap == null)
			return ResultType.MAYBE;
		return reasoner.valid((BooleanExpression) universe
				.mapSubstituter(subMap).apply(newPredicate)).getResultType();
	}

	/**
	 * Return a list of universal quantified expressions in the given boolean
	 * expression. This method will NOT recursively dig in nested universal
	 * quantified expressions.
	 * 
	 * @param predicate
	 *            A boolean expression in which universal quantified expressions
	 *            will be returned.
	 * @return Return a list of universal quantified expressions in the given
	 *         boolean expression.
	 */
	static private List<BooleanExpression> universalQuantifiedExpressionsIn(
			BooleanExpression predicate) {
		List<BooleanExpression> results = new LinkedList<>();

		if (predicate.operator() == SymbolicOperator.AND
				|| predicate.operator() == SymbolicOperator.OR) {
			// clause_0 && clause_1 && ... && clause_n OR
			// clause_0 || clause_1 || ... || clause_n:
			for (SymbolicObject clause : predicate.getArguments())
				results.addAll(universalQuantifiedExpressionsIn(
						(BooleanExpression) clause));
		} else {
			// basic clause:
			if (predicate.operator() == SymbolicOperator.FORALL)
				results.add(predicate);
		}
		return results;
	}

	/**
	 * Given a universal quantified expression with a specific form (see
	 * {@link SymbolicUniverse#getForallStructure(BooleanExpression)}) :
	 * <code>forall int i; lower <= i <= upper ==> predicate(i) </code>, returns
	 * a pair of boolean expressions, the conjunction of which is equivalent to
	 * the given one: <code>
	 * forall int i; lower <= i <= upper-1 ==> predicate(i); 
	 * predicate(upper);
	 * </code> if lower &lt= upper is valid under the context. Otherwise returns
	 * null.
	 * 
	 * @param reasoner
	 *            A reference to a {@link Reasoner} which contains the context.
	 * @param universe
	 *            A reference to a {@link SymbolicUniverse}
	 * @param uniQuant
	 *            The universal quantified expression
	 * @param forall
	 *            An instance of {@link ForallStructure} which is equivalent to
	 *            the universal quantified expression.
	 * @return A pair of boolean expressions, the conjunction of which is
	 *         equivalent to the given universal quantified expression; null if
	 *         aforementioned condition cannot be proved as valid under the
	 *         conext.
	 */
	private static Pair<BooleanExpression, BooleanExpression> universalQuantifiedOneWayExpansion(
			Reasoner reasoner, SymbolicUniverse universe,
			BooleanExpression uniQuant, ForallStructure forall) {
		NumericSymbolicConstant i = forall.boundVariable;

		if (!i.type().isInteger())
			return null;

		NumericExpression lower = forall.lowerBound, upper = forall.upperBound;
		BooleanExpression body = forall.body;
		BooleanExpression requirement = universe.lessThanEquals(lower, upper);

		if (!reasoner.isValid(requirement))
			return null;

		BooleanExpression single = (BooleanExpression) universe
				.simpleSubstituter(i, upper).apply(body);
		BooleanExpression subCases = universe.forallInt(i, lower, upper, body);

		return new Pair<>(single, subCases);
	}

	/**
	 * Given a summation expression:
	 * <code>\sum(lower, upper, \lambda int i; f(i));</code>, returns an
	 * equivalent expression:
	 * <code>\sum(lower, upper-1, \lambda int i; f(i)) + f(upper)</code> if
	 * lower &lt= upper is valid under the context, otherwise return null.
	 * 
	 * @param reasoner
	 *            A reference to a {@link Reasoner} which contains the context.
	 * @param universe
	 *            A reference to a {@link SymbolicUniverse}.
	 * @param sigma
	 *            A summation expression.
	 * @return An equivalent expression to the given summation expression if the
	 *         aforementioned condition holds, otherwise null.
	 */
	static private SymbolicExpression summationOneWayExpansion(
			Reasoner reasoner, SymbolicUniverse universe,
			SymbolicExpression sigma) {
		@SuppressWarnings("unchecked")
		Iterator<SymbolicObject> argIter = ((Iterable<SymbolicObject>) sigma
				.argument(1)).iterator();
		NumericExpression lower = (NumericExpression) argIter.next(),
				upper = (NumericExpression) argIter.next();
		SymbolicExpression foldFunc = (SymbolicExpression) argIter.next();
		BooleanExpression requirement = universe.lessThanEquals(lower, upper);

		if (!reasoner.isValid(requirement))
			return null;

		NumericExpression single = (NumericExpression) universe.apply(foldFunc,
				Arrays.asList(upper));
		NumericExpression subSum = (NumericExpression) universe.sigma(lower,
				universe.subtract(upper, universe.oneInt()), foldFunc);
		return universe.add(single, subSum);
	}

	/**
	 * Returns summation expressions in the given symbolic expression. This
	 * method will NOT recursively dig in nested summation expressions.
	 * 
	 * @param universe
	 *            A reference to {@link SymbolicUniverse}
	 * @param expr
	 * @return A list of summation expressions in the given symbolic expression.
	 */
	static private List<SymbolicExpression> summationsInExpression(
			SymbolicUniverse universe, SymbolicExpression expr) {
		List<SymbolicExpression> results = new LinkedList<>();

		for (SymbolicObject arg : expr.getArguments()) {
			if (arg.symbolicObjectKind() == SymbolicObjectKind.EXPRESSION) {
				SymbolicExpression symExpr = (SymbolicExpression) arg;

				if (universe.isSigmaExpression(symExpr))
					results.add(symExpr);
				else
					results.addAll(summationsInExpression(universe, symExpr));
			}
		}
		return results;
	}
}
