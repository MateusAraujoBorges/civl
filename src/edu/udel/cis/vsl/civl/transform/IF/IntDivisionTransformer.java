package edu.udel.cis.vsl.civl.transform.IF;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;
import edu.udel.cis.vsl.civl.transform.common.IntDivWorker;

/**
 * This transformer is used to replace integer division ('/') and integer modulo
 * ('%') in the program with $int_div(int, int) and $int_mod(int, int) functions
 * respectively.
 * 
 * @author yanyihao
 *
 */
public class IntDivisionTransformer extends BaseTransformer {
	/**
	 * The code (short name) of this transformer.
	 */
	public final static String CODE = "int_division";
	/**
	 * The long name of the transformer.
	 */
	public final static String LONG_NAME = "IntDivisionTransformer";
	/**
	 * The description of this transformer.
	 */
	public final static String SHORT_DESCRIPTION = "transforms division and mod operator in program "
			+ "to $int_div and $int_mod functions";

	public IntDivisionTransformer(ASTFactory astFactory) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		IntDivWorker worker = new IntDivWorker(astFactory);

		return worker.transform(ast);
	}

}
