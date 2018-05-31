package edu.udel.cis.vsl.civl.transform.common;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpParallelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSyncNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.transform.IF.OpenMPOrphanTransformer;

/**
 * TODO add java doc
 * 
 * @author yanyihao
 *
 */
public class OpenMPOrphanWorker extends BaseWorker {

	public OpenMPOrphanWorker(ASTFactory astFactory) {
		super(OpenMPOrphanTransformer.LONG_NAME, astFactory);
		this.identifierPrefix = "$omp_orphan_";
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		SequenceNode<BlockItemNode> root = ast.getRootNode();
		AST newAst;
		Function main = ast.getMain();
		Set<Function> visitedFunctions = new HashSet<>();
		Set<String> globalVars = retrieveVars(root.iterator());

		ast.release();
		searchOMPParallel(main, visitedFunctions, globalVars);
		newAst = astFactory.newAST(root, ast.getSourceFiles(),
				ast.isWholeProgram());
		return newAst;
	}

	/**
	 * Search for #pragma omp parallel blocks.
	 * 
	 * @param visitedFunctions
	 *            Functions that have already been visited.
	 */
	private void searchOMPParallel(Function function,
			Set<Function> visitedFunctions, Set<String> globalVars) {
		if (function == null || function.getDefinition() == null
				|| visitedFunctions.contains(function))
			return;
		else
			visitedFunctions.add(function);

		CompoundStatementNode body = function.getDefinition().getBody();
		Iterator<BlockItemNode> bodyIter = body.iterator();

		while (bodyIter.hasNext()) {
			BlockItemNode item = bodyIter.next();

			if (item instanceof OmpParallelNode) {
				// An #pragma omp parallel statement
				OmpParallelNode ompParallelNode = (OmpParallelNode) item;
				int numChildren = ompParallelNode.numChildren() - 1;
				ASTNode lastNotNullChild = null;

				for (int i = numChildren - 1; i >= 0; i--) {
					ASTNode curNode = ompParallelNode.child(i);

					if (curNode != null) {
						lastNotNullChild = curNode;
						break;
					}
				}
				if (lastNotNullChild instanceof CompoundStatementNode) {
					CompoundStatementNode ompParallelBody = (CompoundStatementNode) lastNotNullChild;
					Set<FunctionDefinitionNode> toBeInserted = searchFunctionToBeInserted(
							ompParallelBody, globalVars);

					ompParallelBody.insertChildren(0,
							new LinkedList<>(toBeInserted));
				}
			}
		}
		for (Function callee : function.getCallees())
			searchOMPParallel(callee, visitedFunctions, globalVars);
	}

	private Set<FunctionDefinitionNode> searchFunctionToBeInserted(ASTNode node,
			Set<String> globalVars) {
		Set<FunctionDefinitionNode> result = new HashSet<>();
		Set<Function> seen = new HashSet<>();
		LinkedList<Function> queue = new LinkedList<>();
		LinkedList<ASTNode> tempQueue = new LinkedList<>();

		tempQueue.add(node);
		while (!tempQueue.isEmpty()) {
			ASTNode n = tempQueue.removeFirst();

			if (n instanceof FunctionCallNode)
				queue.addLast(getFunction((FunctionCallNode) n));
			for (ASTNode child : n.children())
				if (child != null)
					tempQueue.addLast(child);
		}
		while (!queue.isEmpty()) {
			Function curFunction = queue.removeFirst();
			FunctionDefinitionNode functionDefinitionNode = curFunction
					.getDefinition();
			Set<Function> callees = curFunction.getCallees();

			seen.add(curFunction);
			if (containOmpFunctionCallOrPragma(functionDefinitionNode)) {
				functionDefinitionNode.remove();
				result.add(functionDefinitionNode);
			} else if (useSharedVariable(functionDefinitionNode, globalVars)) {
				result.add(functionDefinitionNode.copy());
			}
			for (Function f : callees) {
				if (!seen.contains(f))
					queue.add(f);
			}
		}
		return result;
	}

	/**
	 * 
	 * @param functionDefNode
	 * @return true iff the {@link FunctionDefinitionNode} contains any omp
	 *         function calls.
	 */
	private boolean containOmpFunctionCallOrPragma(
			FunctionDefinitionNode functionDefNode) {
		if (functionDefNode == null)
			return false;
		CompoundStatementNode compoundStatementNode = functionDefNode.getBody();
		Iterator<BlockItemNode> itemsIter = compoundStatementNode.iterator();

		while (itemsIter.hasNext()) {
			BlockItemNode item = itemsIter.next();
			ExpressionNode expressionNode = null;

			if (item instanceof ExpressionStatementNode
					&& (expressionNode = ((ExpressionStatementNode) item)
							.getExpression())
									.expressionKind() == ExpressionKind.FUNCTION_CALL) {
				FunctionCallNode functionCallNode = (FunctionCallNode) expressionNode;
				IdentifierNode identiferNode = ((IdentifierExpressionNode) (functionCallNode
						.getFunction())).getIdentifier();
				String functioName = identiferNode.name();

				if (functioName.startsWith("omp_"))
					return true;
			}
			if (item instanceof OmpForNode || item instanceof OmpSyncNode
					|| item instanceof OmpWorksharingNode)
				return true;
		}
		return false;
	}

	private boolean useSharedVariable(FunctionDefinitionNode functionDefNode,
			Set<String> globalVars) {
		if (functionDefNode == null)
			return false;
		LinkedList<ASTNode> queue = new LinkedList<>();
		Set<String> localVars = retrieveVars(
				functionDefNode.getBody().iterator());

		queue.add(functionDefNode);
		while (!queue.isEmpty()) {
			ASTNode node = queue.removeFirst();

			if (node instanceof IdentifierNode) {
				IdentifierNode idNode = (IdentifierNode) node;

				if (globalVars.contains(idNode.name())
						&& !localVars.contains(idNode.name()))
					return true;
			}
			for (ASTNode child : node.children())
				if (child != null)
					queue.addLast(child);
		}

		return false;
	}

	/**
	 * Get the {@link Function} entity of a {@link FunctionCallNode}.
	 * 
	 * @param functionCallNode
	 *            The target {@link FunctionCallNode}
	 * @return the {@link Function} entity of the target
	 *         {@link FunctionCallNode}.
	 */
	private Function getFunction(FunctionCallNode functionCallNode) {
		ExpressionNode identiferExpression = functionCallNode.getFunction();
		IdentifierExpressionNode identifierExpressionNode = (IdentifierExpressionNode) identiferExpression;
		IdentifierNode identifierNode = identifierExpressionNode
				.getIdentifier();
		Entity entity = identifierNode.getEntity();

		return (Function) entity;
	}

	private Set<String> retrieveVars(Iterator<BlockItemNode> itemsIter) {
		Set<String> vars = new HashSet<>();

		while (itemsIter.hasNext()) {
			BlockItemNode item = (BlockItemNode) itemsIter.next();

			if (item instanceof VariableDeclarationNode) {
				vars.add(((VariableDeclarationNode) item).getIdentifier()
						.name());
			}
		}
		return vars;
	}
}
