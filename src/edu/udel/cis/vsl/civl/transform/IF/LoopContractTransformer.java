package edu.udel.cis.vsl.civl.transform.IF;

import java.io.File;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;
import edu.udel.cis.vsl.civl.transform.common.LoopContractTransformerWorker;

public class LoopContractTransformer extends BaseTransformer {

	private final static String LOOP_ASSIGNS_AUTO_GEN_HEADER = "/include/abc/loop_assigns_gen.cvh";

	private final static String MEM_HEADER = "/include/abc/mem.cvh";

	private final static String STRING_HEADER = "/include/abc/string.h";

	private final static String LOOP_ASSIGNS_AUTO_GEN_IMPL = "/include/civl/loop_assigns_gen.cvl";

	private final static String MEM_IMPL = "/include/civl/mem.cvl";

	private final static String STRING_IMPL = "/include/civl/string.cvl";

	public final static File[] additionalLibraries = {
			new File(LOOP_ASSIGNS_AUTO_GEN_HEADER), new File(MEM_HEADER),
			new File(STRING_HEADER), new File(LOOP_ASSIGNS_AUTO_GEN_IMPL),
			new File(MEM_IMPL), new File(STRING_IMPL)};

	/**
	 * The code (short name) of this transformer.
	 */
	public final static String CODE = "loop";

	/**
	 * The long name of the transformer.
	 */
	public final static String LONG_NAME = "LoopContractTransformer";

	/**
	 * The description of this transformer.
	 */
	public final static String SHORT_DESCRIPTION = "transforms loops contracts"
			+ " into CIVL IR.";

	protected LoopContractTransformer(ASTFactory astFactory) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		return new LoopContractTransformerWorker(LONG_NAME, astFactory)
				.transform(ast);
	}
}
