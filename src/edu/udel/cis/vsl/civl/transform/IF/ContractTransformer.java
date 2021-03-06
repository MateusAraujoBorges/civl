package edu.udel.cis.vsl.civl.transform.IF;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.transform.common.contracts.ContractTransformerWorker;

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
	public final static String SHORT_DESCRIPTION = "transforms C/MPI program "
			+ "to a set of programs each of which verifies a single function";

	private String targetFunction;

	/**
	 * A reference to {@link CIVLConfiguration}
	 */
	private CIVLConfiguration civlConfig;

	public ContractTransformer(ASTFactory astFactory, String targetFunction,
			CIVLConfiguration civlConfig) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
		this.targetFunction = targetFunction;
		this.civlConfig = civlConfig;
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		return new ContractTransformerWorker(astFactory, targetFunction,
				civlConfig).transform(ast);
	}
}
