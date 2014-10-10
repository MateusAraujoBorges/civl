package edu.udel.cis.vsl.civl.transform.common;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.parse.IF.CParser;
import edu.udel.cis.vsl.abc.parse.IF.OmpCParser;
import edu.udel.cis.vsl.abc.token.IF.CToken;
import edu.udel.cis.vsl.abc.token.IF.Formation;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;
import edu.udel.cis.vsl.abc.token.IF.TransformFormation;
import edu.udel.cis.vsl.abc.transform.IF.Transformer;

/**
 * Object used to perform one transformation task. It is instantiated to carry
 * out one invocation of {@link CIVLBaseTransformer#transform(AST)}.
 * 
 * @author siegel
 */
public abstract class BaseWorker {

	/**
	 * The name of this transformer, e.g., "OMPtoCIVLTransformer". To be used in
	 * output such as error messages.
	 */
	protected String transformerName;

	/**
	 * The AST factory used by this transformer for all its AST needs.
	 */
	protected ASTFactory astFactory;

	/**
	 * The node factory used by this transformer; same as the node factory
	 * associated to the {@link #astFactory}.
	 */
	protected NodeFactory nodeFactory;

	/**
	 * The token facotry used by this transformer; same as the token factory
	 * used by the {@link #astFactory}.
	 */
	protected TokenFactory tokenFactory;

	/* ****************************** Constructor ************************** */

	protected BaseWorker(String transformerName, ASTFactory astFactory) {
		this.transformerName = transformerName;
		this.astFactory = astFactory;
		this.nodeFactory = astFactory.getNodeFactory();
		this.tokenFactory = astFactory.getTokenFactory();

	}

	/* *************************** Private Methods ************************* */

	/**
	 * Determins whether the given node is a leaf node, i.e., a node with no
	 * non-null children.
	 * 
	 * @param node
	 *            a non-null AST node
	 * @return true iff node is a leaf node
	 */
	private boolean isLeaf(ASTNode node) {
		for (ASTNode child : node.children()) {
			if (child != null)
				return false;
		}
		return true;
	}

	/**
	 * Finds the next node u after the given node, in DFS order, which satisfies
	 * (1) u is a leaf node, and (2) u contains "actual" source (i.e., not
	 * source generated by a transformer).
	 * 
	 * @param node
	 *            any AST node
	 * @return next leaf node whose first token is actual source, or null if
	 *         there is none
	 */
	private ASTNode nextRealNode(ASTNode node) {
		while (true) {
			node = node.nextDFS();
			if (node == null)
				break;
			if (isLeaf(node)) {
				Source source = node.getSource();

				if (source != null) {
					CToken token = source.getFirstToken();

					if (token != null) {
						Formation formation = token.getFormation();

						if (!(formation instanceof TransformFormation))
							break;
					}
				}
			}
		}
		return node;
	}

	/* ************************** Protected Methods ************************ */

	/**
	 * Transforms the AST. This is the method that will be invoked to implement
	 * {@link Transformer#transform(AST)}.
	 * 
	 * @param ast
	 *            the given AST to transform
	 * @return the transformed AST, which may or may not == the given one
	 * @throws SyntaxException
	 *             if some statically-detectable error is discovered in the
	 *             process of transsformation
	 */
	protected abstract AST transform(AST ast) throws SyntaxException;

	/**
	 * Creates a new {@link Source} object to associate to AST nodes that are
	 * invented by this transformer worker.
	 * 
	 * @param method
	 *            any string which identifies the specific part of this
	 *            transformer responsible for creating the new content;
	 *            typically, the name of the method that created the new
	 *            context. This will appear in error message to help isolate the
	 *            source of the new content.
	 * @param tokenType
	 *            the integer code for the type of the token used to represent
	 *            the source; use one of the constants in {@link CParser} or
	 *            {@link OmpCParser}, for example, such as
	 *            {@link CParser#IDENTIFIER}.
	 * @return the new source object
	 */
	protected Source newSource(String method, int tokenType) {
		Formation formation = tokenFactory.newTransformFormation(
				transformerName, method);
		CToken token = tokenFactory.newCToken(tokenType, "inserted text",
				formation);
		Source source = tokenFactory.newSource(token);

		return source;
	}

	/**
	 * This method should be called after the transformer has completed its
	 * transformation; it finds all source objects (in node and the descendants
	 * of node) that were created by this transformer and adds more information
	 * to them. The new information includes the pretty-print textual
	 * representation of the content of that node (and its descendants), and the
	 * precise point in original actual source code where the new content was
	 * inserted.
	 * 
	 * @param node
	 *            a node in the AST being transformed; typically, the root node
	 */
	protected void completeSources(ASTNode node) {
		ASTNode postNode = nextRealNode(node);
		ASTNode preNode = null;

		for (; node != null; node = node.nextDFS()) {
			Source source = node.getSource();

			if (source != null) {
				CToken firstToken = source.getFirstToken();

				if (firstToken != null) {
					Formation formation = firstToken.getFormation();

					if (formation instanceof TransformFormation) {
						TransformFormation tf = (TransformFormation) formation;

						if (transformerName.equals(tf.getLastFile().getName())) {
							CToken preToken = preNode == null ? null : preNode
									.getSource().getLastToken();
							CToken postToken = postNode == null ? null
									: postNode.getSource().getFirstToken();
							ByteArrayOutputStream bastream = new ByteArrayOutputStream();
							PrintStream stream = new PrintStream(bastream);
							String text;

							node.prettyPrint(stream);
							text = stream.toString();
							stream.close();
							tf.setPreToken(preToken);
							tf.setPostToken(postToken);
							firstToken.setText(text);
						} else {
							if (node == postNode) {
								preNode = postNode;
								postNode = nextRealNode(preNode);
							}
						}
					}
				}
			}
		}
	}

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

	/**
	 * TODO: javadocs
	 * 
	 * @param node
	 * @return
	 */
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

	/**
	 * TODO javadocs
	 * 
	 * @param source
	 * @param name
	 * @param type
	 * @return
	 */
	protected VariableDeclarationNode variableDeclaration(Source source,
			String name, TypeNode type) {
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, name), type);
	}

	protected VariableDeclarationNode variableDeclaration(Source source,
			String name, TypeNode type, ExpressionNode init) {
		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, name), type, init);
	}

	protected TypeNode typeNode(Source source, Type type) {
		switch (type.kind()) {
		case VOID:
			return nodeFactory.newVoidTypeNode(source);
		case BASIC:
			return nodeFactory.newBasicTypeNode(source,
					((StandardBasicType) type).getBasicTypeKind());
		case OTHER_INTEGER:
			return nodeFactory.newBasicTypeNode(source, BasicTypeKind.INT);
		case ARRAY:
			return nodeFactory.newArrayTypeNode(source,
					this.typeNode(source, ((ArrayType) type).getElementType()),
					((ArrayType) type).getVariableSize().copy());
		case POINTER:
			return nodeFactory.newPointerTypeNode(source, this.typeNode(source,
					((PointerType) type).referencedType()));
		default:
		}
		return null;
	}

}
