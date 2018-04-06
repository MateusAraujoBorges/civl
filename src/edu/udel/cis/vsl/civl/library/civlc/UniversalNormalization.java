package edu.udel.cis.vsl.civl.library.civlc;

import edu.udel.cis.vsl.sarl.IF.CoreUniverse.ForallStructure;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.Number;

/**
 * <p>
 * Briefly, this transformer tries to force the lower bound of the bound
 * variable of a universal quantified expression to be zero.
 * </p>
 * 
 * <p>
 * A transformer that transforms:
 * <code>forall int i: l <= i < h -> pred(i)</code> to
 * <code>forall int i: 0 <= i < h - l -> pred(i+l)</code> iff <code>l</code> is
 * a concrete constant.
 * </p>
 * 
 * @author ziqing
 *
 */
public class UniversalNormalization extends ExpressionVisitor
		implements
			UnaryOperator<SymbolicExpression> {

	private SymbolicUniverse universe;

	public UniversalNormalization(SymbolicUniverse universe) {
		super(universe);
		this.universe = universe;
	}

	@Override
	public SymbolicExpression apply(SymbolicExpression expr) {
		return visitExpression(expr);
	}

	@Override
	SymbolicExpression visitExpression(SymbolicExpression expr) {
		expr = visitExpressionChildren(expr);
		if (expr.operator() != SymbolicOperator.FORALL)
			return expr;

		ForallStructure forall = universe
				.getForallStructure((BooleanExpression) expr);

		if (forall == null)
			return expr;

		NumericExpression lower = forall.lowerBound;
		NumericExpression upper, boundVarReplacer;
		BooleanExpression body;
		Number lowerNumber = universe.extractNumber(lower);

		if (lowerNumber == null || lowerNumber.isZero())
			return expr;
		upper = universe.subtract(forall.upperBound, lower);
		boundVarReplacer = universe.add(forall.boundVariable, lower);
		body = (BooleanExpression) universe
				.simpleSubstituter(forall.boundVariable, boundVarReplacer)
				.apply(forall.body);
		return universe.forallInt(forall.boundVariable, universe.zeroInt(),
				universe.add(upper, universe.oneInt()), body);
	}
}
