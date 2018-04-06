package edu.udel.cis.vsl.civl.library.civlc;

import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class Heuristics {

	private SymbolicUniverse universe;

	public static class Query {
		public final BooleanExpression context;
		public final BooleanExpression query;

		public Query(BooleanExpression context, BooleanExpression query) {
			this.context = context;
			this.query = query;
		}
	}

	public Heuristics(SymbolicUniverse universe) {
		this.universe = universe;
	}

	public Query applyHeuristicSimplifications(BooleanExpression context,
			BooleanExpression predicate) {
		UnaryOperator<SymbolicExpression> simplifier = new SteppedUniversalCombination(
				universe);

		context = (BooleanExpression) simplifier.apply(context);
		predicate = (BooleanExpression) simplifier.apply(predicate);

		simplifier = new ArrayReadOverWriteSimplification(universe, context);
		context = (BooleanExpression) simplifier.apply(context);
		predicate = (BooleanExpression) simplifier.apply(predicate);

		return new Query(context, predicate);
	}
}
