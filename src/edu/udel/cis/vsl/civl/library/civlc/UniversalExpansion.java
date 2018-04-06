package edu.udel.cis.vsl.civl.library.civlc;

import edu.udel.cis.vsl.sarl.IF.CoreUniverse.ForallStructure;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;

public class UniversalExpansion extends ExpressionVisitor
		implements
			UnaryOperator<SymbolicExpression> {

	private Reasoner reasoner;

	UniversalExpansion(SymbolicUniverse universe, Reasoner reasoner) {
		super(universe);
		this.reasoner = reasoner;
	}

	@Override
	public SymbolicExpression apply(SymbolicExpression x) {
		return visitExpression(x);
	}

	@Override
	SymbolicExpression visitExpression(SymbolicExpression expr) {
		if (expr.operator() == SymbolicOperator.FORALL) {
			ForallStructure forallStructure = universe
					.getForallStructure((BooleanExpression) expr);

			if (forallStructure != null) {
				if (reasoner
						.isValid(universe.lessThan(forallStructure.lowerBound,
								forallStructure.upperBound))) {

					NumericExpression lower = forallStructure.lowerBound;
					BooleanExpression lowestCase = (BooleanExpression) universe
							.simpleSubstituter(forallStructure.boundVariable,
									lower)
							.apply(forallStructure.body);
					BooleanExpression newForall = universe.forallInt(
							forallStructure.boundVariable,
							universe.subtract(forallStructure.lowerBound,
									universe.oneInt()),
							universe.add(forallStructure.upperBound,
									universe.oneInt()),
							forallStructure.body);

					// NumericExpression upper = forallStructure.upperBound;
					// BooleanExpression upMostCase = (BooleanExpression)
					// universe
					// .simpleSubstituter(forallStructure.boundVariable, upper)
					// .apply(forallStructure.body);
					// BooleanExpression newForall = universe.forallInt(
					// forallStructure.boundVariable,
					// forallStructure.lowerBound, forallStructure.upperBound,
					// forallStructure.body);

					return universe.and(lowestCase, newForall);
				}
			}
		}
		return visitExpressionChildren(expr);
	}
}
