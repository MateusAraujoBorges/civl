package edu.udel.cis.vsl.civl.transform.IF;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;
import edu.udel.cis.vsl.civl.transform.common.ContractTransformerWorker;

public class ContractTransformer extends BaseTransformer {

	/**
	 * The code (short name) of this transformer.
	 */
	public final static String CODE = "contract";

	/**
	 * The long name of the transformer.
	 */
	public final static String LONG_NAME = "ContractTransformer";

	/**
	 * The description of this transformer.
	 */
	public final static String SHORT_DESCRIPTION = "transforms C/MPI program to a set of programs each of which verifies a single function";

	private String targetFunction;

	public ContractTransformer(ASTFactory astFactory, String targetFunction) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
		this.targetFunction = targetFunction;
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		return new ContractTransformerWorker(astFactory, targetFunction)
				.transform(ast);
	}
}
