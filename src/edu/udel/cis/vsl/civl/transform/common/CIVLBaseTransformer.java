package edu.udel.cis.vsl.civl.transform.common;

import java.util.List;

import edu.udel.cis.vsl.abc.antlr2ast.IF.ASTBuilder;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;

/**
 * This is the base transformer of CIVL. Any transformer implemented in CIVL
 * should extend this class. This class extends BaseTransformer (from ABC) and
 * provides extra instance fields and common methods to be used by any
 * particular transformers.
 * 
 * @author Manchun Zheng
 * 
 */
public abstract class CIVLBaseTransformer extends BaseTransformer {

	/* **************************** Instant Fields ************************* */

	/**
	 * The list of variable names that appear in "-input" options specified by
	 * users in CIVL's command line.
	 */
	protected List<String> inputVariableNames;

	/**
	 * The AST builder to be reused in the transformer to parse tokens. For
	 * example, the OpenMP pragma transformer uses the AST builder to parse
	 * expressions.
	 */
	protected ASTBuilder astBuilder;

	/**
	 * The flag to turn on/off debugging. Useful for printing more information
	 * in debug mode.
	 */
	protected boolean debug;

	/* ****************************** Constructor ************************** */

	/**
	 * Creates a new instance of CIVLBaseTransformer.
	 * 
	 * @param code
	 *            The code of the transformer.
	 * @param longName
	 *            The full name of the transformer.
	 * @param shortDescription
	 *            The description of the transformer.
	 * @param astFactory
	 *            The ASTFactory that will be used to create new AST nodes.
	 * 
	 */
	protected CIVLBaseTransformer(String code, String longName,
			String shortDescription, ASTFactory astFactory,
			List<String> inputVariables, ASTBuilder astBuilder, boolean debug) {
		super(code, longName, shortDescription, astFactory);
		this.inputVariableNames = inputVariables;
		this.astBuilder = astBuilder;
		this.debug = debug;
	}

	/**
	 * Creates a new instance of CIVLBaseTransformer.
	 * 
	 * @param code
	 *            The code of the transformer.
	 * @param longName
	 *            The full name of the transformer.
	 * @param shortDescription
	 *            The description of the transformer.
	 * @param astFactory
	 *            The ASTFactory that will be used to create new AST nodes.
	 * 
	 */
	protected CIVLBaseTransformer(String code, String longName,
			String shortDescription, ASTFactory astFactory,
			List<String> inputVariables, boolean debug) {
		super(code, longName, shortDescription, astFactory);
		this.inputVariableNames = inputVariables;
		this.debug = debug;
	}

	/**
	 * Creates a new instance of CIVLBaseTransformer.
	 * 
	 * @param code
	 *            The code of the transformer.
	 * @param longName
	 *            The full name of the transformer.
	 * @param shortDescription
	 *            The description of the transformer.
	 * @param astFactory
	 *            The ASTFactory that will be used to create new AST nodes.
	 * 
	 */
	protected CIVLBaseTransformer(String code, String longName,
			String shortDescription, ASTFactory astFactory, boolean debug) {
		super(code, longName, shortDescription, astFactory);
		this.debug = debug;
	}

	/* ************************** Protected Methods ************************ */

	/**
	 * Creates an identifier expression node with a given name.
	 * 
	 * @param source
	 *            The source information of the identifier.
	 * @param name
	 *            The name of the identifier.
	 * @return
	 */
	protected ExpressionNode identifierExpression(Source source, String name) {
		return nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, name));
	}

	protected Source getMainSource(ASTNode node) {
		if (node.nodeKind() == NodeKind.FUNCTION_DEFINITION) {
			FunctionDefinitionNode functionNode = (FunctionDefinitionNode) node;
			IdentifierNode functionName = (IdentifierNode) functionNode
					.child(0);

			if (functionName.name().equals("main")) {
				return node.getSource();
			}
		}
		for (ASTNode child : node.children()) {
			if (child == null)
				continue;
			else {
				Source childResult = getMainSource(child);

				if (childResult != null)
					return childResult;
			}
		}
		return null;
	}

	/* *************************** Public Methods ************************* */

	/**
	 * Updates the list of names of input variables.
	 * 
	 * @param inputVars
	 */
	public void setInputVars(List<String> inputVars) {
		this.inputVariableNames = inputVars;
	}

	/**
	 * Updates the AST builder.
	 * 
	 * @param astBuilder
	 */
	public void setASTBuilder(ASTBuilder astBuilder) {
		this.astBuilder = astBuilder;
	}

}
