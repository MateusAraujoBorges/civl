package edu.udel.cis.vsl.civl.transform.IF;

import java.util.Map;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;
import edu.udel.cis.vsl.civl.transform.common.IntOperationWorker;

/**
 * This transformer is used to replace integer division ('/') and integer modulo
 * ('%') in the program with $int_div(int, int) and $int_mod(int, int) functions
 * respectively.
 * 
 * @author yanyihao
 *
 */
public class IntOperationTransformer extends BaseTransformer {
	/**
	 * The code (short name) of this transformer.
	 */
	public final static String CODE = "int_operation";
	/**
	 * The long name of the transformer.
	 */
	public final static String LONG_NAME = "IntOperationTransformer";
	/**
	 * The description of this transformer.
	 */
	public final static String SHORT_DESCRIPTION = "transform division and mod operator in program "
			+ "to $int_div and $int_mod functions"
			+ " and unsigned integer arithmetic operation (add, substract, multiply)"
			+ " into $unsigned_add, $unsigned_subtract and $unsigned_multiply functions"
			+ " respectively.";

	private Map<String, String> macros;

	public IntOperationTransformer(ASTFactory astFactory,
			Map<String, String> macros) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
		this.macros = macros;
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		IntOperationWorker worker = new IntOperationWorker(astFactory, macros);

		return worker.transform(ast);
	}

}
