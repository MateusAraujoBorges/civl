package edu.udel.cis.vsl.civl.library.civlc;

import java.util.Iterator;

import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.UnaryOperator;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;

/**
 * This transformer attempts to get rid of ARRAY_WRITE expressions that is read
 * by an ARRAY_READ expression if one can prove that
 * <code>array-write-index != array-read-index</code> or replace the ARRAY_READ
 * expression with the written value of the ARRAY_WRITE expression if one can
 * prove that <code>array-write-index == array-read-index</code>.
 * 
 * @author ziqing
 *
 */
public class ArrayReadOverWriteSimplification extends ExpressionVisitor
		implements
			UnaryOperator<SymbolicExpression> {

	private SymbolicUniverse universe;

	ArrayReadOverWriteSimplification(SymbolicUniverse universe,
			BooleanExpression context) {
		super(universe);
		this.universe = universe;
	}

	@Override
	public SymbolicExpression apply(SymbolicExpression x) {
		return visitExpression(x);
	}

	private SymbolicExpression readArrayWrite(SymbolicExpression arrayWrite,
			NumericExpression index) {
		SymbolicExpression array = (SymbolicExpression) arrayWrite.argument(0);
		NumericExpression wrtIndex = (NumericExpression) arrayWrite.argument(1);
		BooleanExpression neq = universe.neq(wrtIndex, index);
		BooleanExpression eq = universe.equals(wrtIndex, index);

		if (neq.isTrue()) {
			if (array.operator() == SymbolicOperator.ARRAY_WRITE)
				return readArrayWrite(array, index);

			if (array.operator() == SymbolicOperator.DENSE_ARRAY_WRITE)
				return readDenseArrayWrite(array, index);
			return universe.arrayRead(array, index);
		}
		if (eq.isTrue())
			return (SymbolicExpression) arrayWrite.argument(2);
		return universe.arrayRead(arrayWrite, index);
	}

	private SymbolicExpression readDenseArrayWrite(
			SymbolicExpression arrayDenseWrite, NumericExpression index) {
		SymbolicExpression array = (SymbolicExpression) arrayDenseWrite
				.argument(0);
		@SuppressWarnings("unchecked")
		Iterable<SymbolicExpression> values = (Iterable<SymbolicExpression>) arrayDenseWrite
				.argument(1);
		Iterator<SymbolicExpression> iter = values.iterator();
		int counter = 0;

		// TODO: temporary compromising ...
		while (iter.hasNext()) {
			iter.next();
			counter++;
		}
		if (counter != 1)
			return universe.arrayRead(arrayDenseWrite, index);

		NumericExpression wrtIndex = universe.zeroInt();
		BooleanExpression neq = universe.neq(wrtIndex, index);
		BooleanExpression eq = universe.equals(wrtIndex, index);

		if (neq.isTrue()) {
			if (array.operator() == SymbolicOperator.ARRAY_WRITE)
				return readArrayWrite(array, index);
			if (array.operator() == SymbolicOperator.DENSE_ARRAY_WRITE)
				return readDenseArrayWrite(array, index);
			return universe.arrayRead(array, index);
		}
		if (eq.isTrue())
			return values.iterator().next();
		return universe.arrayRead(arrayDenseWrite, index);
	}

	@Override
	SymbolicExpression visitExpression(SymbolicExpression expr) {
		expr = visitExpressionChildren(expr);
		if (expr.operator() == SymbolicOperator.ARRAY_READ) {
			SymbolicExpression array = (SymbolicExpression) expr.argument(0);
			NumericExpression index = (NumericExpression) expr.argument(1);

			// TODO: check wrtIndex == index
			// TODO: use reasoner ?
			// TODO: dense array write
			if (array.operator() == SymbolicOperator.ARRAY_WRITE)
				return readArrayWrite(array, index);
			else if (array.operator() == SymbolicOperator.DENSE_ARRAY_WRITE)
				return readDenseArrayWrite(array, index);
		}
		return expr;
	}
}
