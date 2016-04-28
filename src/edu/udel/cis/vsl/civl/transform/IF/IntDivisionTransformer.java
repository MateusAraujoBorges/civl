package edu.udel.cis.vsl.civl.transform.IF;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;
import edu.udel.cis.vsl.civl.transform.common.IntDivWorker;;

public class IntDivisionTransformer extends BaseTransformer{
	public final static String CODE = "int division";
	public final static String LONG_NAME = "IntDivisionTransformer";
	public final static String SHORT_DESCRIPTION = "transforms division and mod operator in program "
			+ "to $int_div and $int_mod functions";

	public IntDivisionTransformer(ASTFactory astFactory) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		return new IntDivWorker(astFactory).transform(ast);
	}
}