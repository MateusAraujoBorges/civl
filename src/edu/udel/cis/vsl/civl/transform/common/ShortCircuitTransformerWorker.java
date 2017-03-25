package edu.udel.cis.vsl.civl.transform.common;

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.OrdinaryDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.OrdinaryDeclarationNode.OrdinaryDeclarationKind;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.TypedefDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.label.LabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode.BlockItemKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.IfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode.LoopKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode.StatementKind;
import edu.udel.cis.vsl.abc.ast.node.IF.type.StructureOrUnionTypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * <p>
 * This class is a program transformer for getting rid of short circuit
 * evaluations. i.e. Transform away the following three operators: logical AND,
 * logical OR and logical IMPLIES:
 * </p>
 *
 * <p>
 * The basic idea is:<code>a AND b</code> is transformed to <code>
 * _Bool _tmp_ = a;
 * 
 * if (_tmp_) _tmp_ = b;
 * </code>. <br>
 * <code>a OR b</code> is transformed to <code>
 * _Bool _tmp_ = a;
 * 
 * if (!_tmp_) _tmp_ = b;
 * </code>. <br>
 * <code>a IMPLIES b <==> !a OR b</code> is transformed to <code>
 * _Bool _tmp_ = !a;
 * 
 * if (!_tmp_) _tmp_ = b;
 * </code>.
 * </p>
 * 
 * <p>
 * Defines a function
 * <code>stmt-sequence  transform(expr e, identifier var)</code>, it takes an
 * expression e which contains short-circuit operators and an identifier var,
 * transforms e into a sequence of statements S and guarantees the var holds the
 * evaluation of e after executing S.
 * 
 * <br>
 * Example: <code>
 * $assert( (a && b && !c) || d ==> e && a ); </code>will be transformed
 * as<code> 
 * let P0 denotes  (a && b && !c)
 * let P1 denotes d
 * let P2 denotes e && a
 * then it becomes 
 * $assert( P0 || P1 ==> P2 );
 * 
 *  _Bool tmp;
 *  
 *  transform(P0, &tmp);
 *  if (!tmp) transform(P1, &tmp);
 *  tmp = !tmp;
 *  if (!tmp)
 *     transform(P2, &tmp);
 *  $assert( tmp );
 * </code>
 *
 * </p>
 * 
 * @author ziqingluo
 *
 */
public class ShortCircuitTransformerWorker extends BaseWorker {

	static private final String SCTransformer_PREFIX = "_scc";

	static private final String HOLDER_PREFIX = SCTransformer_PREFIX + "_h";

	static private final String LABEL_PREFIX = SCTransformer_PREFIX + "_label";

	private int generatedVariableCounter = 0;

	private class ShortCircuitRemover {
		/**
		 * The original expression in the old ASTree. it must refer to its'
		 * parent.
		 */
		ExpressionNode originalExpression;

		/**
		 * The {@link BlockItemNode} who owns the original expression and marks
		 * the position before where the transformed statements should be
		 * inserted in.
		 */
		BlockItemNode expressionOwner;

		/**
		 * A list of transformed statements, execution of which delivers the
		 * evaluation (with short-circuit semantics) of the original expression.
		 * None of the node in this list is a part of the old ASTree.
		 */
		LinkedList<BlockItemNode> statements = null;

		/**
		 * The name of the identifier of a temporary variable which will hold
		 * the evaluation of the original expression after executing the
		 * transformed statements.
		 */
		String identifierName = null;

		ShortCircuitRemover(ExpressionNode expression, BlockItemNode location) {
			this.originalExpression = expression;
			this.expressionOwner = location;
		}

		void complete(LinkedList<BlockItemNode> statements,
				String identifierName) {
			this.statements = statements;
			this.identifierName = identifierName;
		}

		boolean isInLoopCondition() {
			if (this.expressionOwner
					.blockItemKind() == BlockItemKind.STATEMENT) {
				return ((StatementNode) expressionOwner)
						.statementKind() == StatementKind.LOOP;
			}
			return false;
		}

		@Override
		public String toString() {
			return this.originalExpression.toString();
		}
	}

	static private boolean isShortCircuitOperator(Operator oprt) {
		return oprt == Operator.LAND || oprt == Operator.LOR
				|| oprt == Operator.IMPLIES;
	}

	static private boolean isBoundedExpression(ExpressionNode expr) {
		ExpressionKind kind = expr.expressionKind();

		return kind == ExpressionKind.QUANTIFIED_EXPRESSION
				|| kind == ExpressionKind.ARRAY_LAMBDA
				|| kind == ExpressionKind.LAMBDA
				|| kind == ExpressionKind.ARRAY_LAMBDA;
	}

	static private boolean isArgumentOfWhen(ExpressionNode expr) {
		if (expr.parent().nodeKind() == NodeKind.STATEMENT) {
			StatementNode stmt = (StatementNode) expr.parent();

			return stmt.statementKind() == StatementKind.WHEN;
		}
		return false;
	}

	private String nextHolderName() {
		return HOLDER_PREFIX + generatedVariableCounter++;
	}

	private String nextLabelName() {
		return LABEL_PREFIX + generatedVariableCounter++;
	}

	public ShortCircuitTransformerWorker(String transformerName,
			ASTFactory astFactory) {
		super(transformerName, astFactory);
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		List<ShortCircuitRemover> removers = new LinkedList<>();
		SequenceNode<BlockItemNode> rootNode = ast.getRootNode();

		ast.release();
		// Find out all expressions containing short-circuit operators:
		for (BlockItemNode subTree : rootNode)
			removers.addAll(searchSCInBlockItem(subTree));
		// Generating transformed statements to deliver the short-circuit
		// semantics:
		for (ShortCircuitRemover remover : removers)
			transformShortCircuitExpression(remover);

		// Special transformation for loop condition:
		Map<BlockItemNode, BlockItemNode> seenLoops = new HashMap<>();

		for (ShortCircuitRemover remover : removers)
			if (remover.isInLoopCondition()) {
				transformShortCircuitLoopCondition(remover, seenLoops);
			}
		// Inserts transformed statements and replaces expressions with
		// temporary variables:
		for (ShortCircuitRemover remover : removers)
			mountTransformedSCExpressions(remover);
		ast = astFactory.newAST(rootNode, ast.getSourceFiles(),
				ast.isWholeProgram());
		// ast.prettyPrint(System.out, true);
		return ast;
	}

	void mountTransformedSCExpressions(ShortCircuitRemover remover) {
		BlockItemNode location = remover.expressionOwner;
		ExpressionNode holderExpression = identifierExpression(
				remover.identifierName);
		ExpressionNode originalExpression = remover.originalExpression;
		ASTNode locationParent = location.parent();
		int locationChildIdx = location.childIndex();

		if (locationParent.nodeKind() == NodeKind.SEQUENCE) {
			@SuppressWarnings("unchecked")
			SequenceNode<BlockItemNode> seqNode = (SequenceNode<BlockItemNode>) locationParent;

			seqNode.insertChildren(locationChildIdx, remover.statements);
		} else if (locationParent instanceof CompoundStatementNode) {
			CompoundStatementNode compound = (CompoundStatementNode) locationParent;

			compound.insertChildren(locationChildIdx, remover.statements);
		} else {
			StatementNode locationReplacer;

			location.remove();
			remover.statements.add(location);
			locationReplacer = nodeFactory.newCompoundStatementNode(
					location.getSource(), remover.statements);
			locationParent.setChild(locationChildIdx, locationReplacer);
		}
		ASTNode oriExprParent = originalExpression.parent();
		int oriExprChildIdx = originalExpression.childIndex();

		originalExpression.remove();
		oriExprParent.setChild(oriExprChildIdx, holderExpression);
	}

	private List<ShortCircuitRemover> searchSCInBlockItem(
			BlockItemNode subTree) {
		if (subTree == null)
			return Arrays.asList();

		BlockItemKind kind = subTree.blockItemKind();
		List<ShortCircuitRemover> SCRemovers = new LinkedList<>();

		switch (kind) {
			case STATEMENT :
				SCExpressionSearcher(subTree, subTree, SCRemovers);
				break;
			case STRUCT_OR_UNION :
				StructureOrUnionTypeNode typeNode = (StructureOrUnionTypeNode) subTree;

				SCExpressionSearcher(typeNode, subTree, SCRemovers);
				break;
			case TYPEDEF :
				TypedefDeclarationNode typedefNode = (TypedefDeclarationNode) subTree;

				SCExpressionSearcher(typedefNode.getTypeNode(), subTree,
						SCRemovers);
				break;
			case ORDINARY_DECLARATION :
				OrdinaryDeclarationNode declNode = (OrdinaryDeclarationNode) subTree;

				SCExpressionSearcher(declNode.getTypeNode(), subTree,
						SCRemovers);
				if (declNode
						.ordinaryDeclarationKind() == OrdinaryDeclarationKind.FUNCTION_DEFINITION) {
					FunctionDefinitionNode funcDefiNode = (FunctionDefinitionNode) declNode;

					// No need to look at formal parameters because they will be
					// treated as if expressions were replaced by *:
					SCExpressionSearcher(funcDefiNode.getBody(), subTree,
							SCRemovers);
				}
				break;
			case PRAGMA :
				// when are pragma nodes translated away ?
			case STATIC_ASSERTION :
				// no-op
			case ENUMERATION :
				// no-op
			case OMP_DECLARATIVE :
				// no-op
			default :
				break;
		}
		return SCRemovers;
	}

	private void searchSCInExpression(ExpressionNode expression,
			BlockItemNode location, List<ShortCircuitRemover> output) {
		if (isBoundedExpression(expression))
			// Cannot transform quantified expressions.
			return;

		if (expression.expressionKind() == ExpressionKind.OPERATOR) {
			Operator oprt = ((OperatorNode) expression).getOperator();

			if (isShortCircuitOperator(oprt)) {
				output.add(new ShortCircuitRemover(expression, location));
				// Never search sub-expressions
				return;
			}
		}
		SCExpressionSearcher(expression, location, output);
	}

	private void SCExpressionSearcher(ASTNode node, BlockItemNode location,
			List<ShortCircuitRemover> output) {
		for (ASTNode child : node.children()) {
			if (child == null)
				continue;
			if (child.nodeKind() == NodeKind.STATEMENT)
				SCExpressionSearcher(child, (StatementNode) child, output);
			else if (child.nodeKind() == NodeKind.EXPRESSION) {
				if (!isArgumentOfWhen((ExpressionNode) child))
					searchSCInExpression((ExpressionNode) child, location,
							output);
			} else {
				if (child instanceof BlockItemNode)
					SCExpressionSearcher(child, (BlockItemNode) child, output);
				else
					SCExpressionSearcher(child, location, output);
			}
		}
	}

	/* *********** Special Transformation for SC loop conditions **************/
	private void transformShortCircuitLoopCondition(ShortCircuitRemover remover,
			Map<BlockItemNode, BlockItemNode> seenLoops) {
		LoopNode loop = (LoopNode) remover.expressionOwner;
		BlockItemNode newOwner;

		// Manipulate while loop and for loop as follows:
		// while (cond) stmt ==> while (true) if (!cond) break; else stmt
		// for (cond) stmt ==> for (true) if (!cond) break; else stmt
		// do_while doen't need transformation.
		// For the first two cases, the evaluation of the short-circuit
		// expression will be inserted immediately before the if-statements; For
		// the third one, usually it will be inserted at the end of the loop.
		// However, if the loop contains continue, the transformation will
		// non-trivially make it be as follows:
		// do stmt while(cond) ==> stmt while(true) if (!cond) break; else
		// stmt;
		if (seenLoops.containsKey(loop)) {
			newOwner = seenLoops.get(loop);

			remover.expressionOwner = newOwner;
			return;
		}
		if (loop.getKind() != LoopKind.DO_WHILE)
			newOwner = transformConditionFirstLoop(loop, remover);
		else
			newOwner = transformBodyFirstLoop(loop, remover);
		seenLoops.put(loop, newOwner);
	}

	// while, for loops
	private BlockItemNode transformConditionFirstLoop(LoopNode loop,
			ShortCircuitRemover remover) {
		ExpressionNode loopCondition = loop.getCondition();
		StatementNode body = loop.getBody();
		StatementNode ifElseNode;

		loopCondition.remove();
		body.remove();
		ifElseNode = nodeFactory.newIfNode(loopCondition.getSource(),
				loopCondition, body,
				nodeFactory.newBreakNode(loop.getSource()));
		loop.setBody(ifElseNode);
		loop.setCondition(nodeFactory
				.newBooleanConstantNode(loopCondition.getSource(), true));
		remover.expressionOwner = ifElseNode;
		return ifElseNode;
	}

	// do-while loop
	private BlockItemNode transformBodyFirstLoop(LoopNode loop,
			ShortCircuitRemover remover) {
		// Non-trivial transformation, unrolling the first iteration:
		// do stmt while (cond) ==>
		// stmt do if (cond) stmt else break while(true);
		StatementNode body = loop.getBody();
		ExpressionNode loopCondition = loop.getCondition();
		StatementNode ifElseNode;
		StatementNode skipConditionEvaluation;
		StatementNode newBlock; // unrolled iteration followed by the loop.
		StatementNode newLoop;
		Source source = loop.getSource();
		IdentifierNode labelName = identifier(nextLabelName());
		LabelNode label;

		loopCondition.remove();
		body.remove();
		label = nodeFactory.newStandardLabelDeclarationNode(source, labelName,
				body);
		body = nodeFactory.newLabeledStatementNode(source, label, body);
		ifElseNode = nodeFactory.newIfNode(loopCondition.getSource(),
				loopCondition, body, nodeFactory.newBreakNode(source));
		skipConditionEvaluation = nodeFactory.newGotoNode(source,
				labelName.copy());
		newLoop = nodeFactory.newWhileLoopNode(source,
				nodeFactory.newBooleanConstantNode(source, true), ifElseNode,
				null);
		remover.expressionOwner = ifElseNode;

		ASTNode parent = loop.parent();
		int loopIdx = loop.childIndex();

		loop.remove();
		newBlock = nodeFactory.newCompoundStatementNode(source,
				Arrays.asList(skipConditionEvaluation, newLoop));
		parent.setChild(loopIdx, newBlock);
		return ifElseNode;
	}
	/* **************** generating transformation statements ******************/
	private void transformShortCircuitExpression(ShortCircuitRemover remover) {
		String holderName = nextHolderName();
		LinkedList<BlockItemNode> transfromStatements = new LinkedList<>();
		VariableDeclarationNode holderDecl = nodeFactory
				.newVariableDeclarationNode(
						remover.originalExpression.getSource(),
						identifier(holderName), basicType(BasicTypeKind.BOOL));
		List<StatementNode> evaluationStatements = transformShortCircuitExpressionWorker(
				remover.originalExpression, holderName);

		transfromStatements.add(holderDecl);
		for (BlockItemNode evalStmt : evaluationStatements)
			transfromStatements.add(evalStmt);
		remover.complete(transfromStatements, holderName);
	}

	private List<StatementNode> transformShortCircuitExpressionWorker(
			ExpressionNode expression, String holderName) {
		if (isBoundedExpression(expression))
			return Arrays.asList();
		if (expression.expressionKind() == ExpressionKind.OPERATOR) {
			OperatorNode oprtNode = (OperatorNode) expression;

			if (isShortCircuitOperator(oprtNode.getOperator())) {
				ExpressionNode left = oprtNode.getArgument(0);
				ExpressionNode right = oprtNode.getArgument(1);
				Source source = oprtNode.getSource();

				if (oprtNode.getOperator() == Operator.LAND)
					return transformShortCircuitExpressionWorker_LAND(left,
							right, holderName, source);
				else if (oprtNode.getOperator() == Operator.LOR)
					return transformShortCircuitExpressionWorker_LOR(left,
							right, holderName, source);
				else
					return transformShortCircuitExpressionWorker_IMPLIES(left,
							right, holderName, source);
			}
		}

		List<StatementNode> result = new LinkedList<>();
		ExpressionNode expressionClone = expression.copy();

		for (ASTNode child : expression.children())
			if (child != null && child.nodeKind() == NodeKind.EXPRESSION) {
				List<StatementNode> subResult = transformShortCircuitExpressionWorker(
						(ExpressionNode) child, holderName);

				if (!subResult.isEmpty()) {
					result.addAll(subResult);

					expressionClone.setChild(child.childIndex(),
							identifierExpression(holderName));
				}
			}
		if (!result.isEmpty()) {
			ExpressionNode assignSubExpression2Holder = nodeFactory
					.newOperatorNode(expression.getSource(), Operator.ASSIGN,
							Arrays.asList(identifierExpression(holderName),
									expressionClone));

			result.add(nodeFactory
					.newExpressionStatementNode(assignSubExpression2Holder));
		}
		return result;
	}

	private List<StatementNode> transformShortCircuitExpressionWorker_LAND(
			ExpressionNode left, ExpressionNode right, String holderName,
			Source source) {
		List<StatementNode> results;
		ExpressionNode holderExpr = identifierExpression(holderName);
		StatementNode rightEvaluation;
		IfNode ifNode;

		results = transformSCLeftOperand(left, holderName);
		rightEvaluation = transformSCRightOperand(right, holderName);

		if (rightEvaluation == null) {
			// If there is no SC operator in right expression, holder =
			// rightExpression;
			ExpressionNode assign = nodeFactory.newOperatorNode(
					right.getSource(), Operator.ASSIGN,
					Arrays.asList(holderExpr, right.copy()));

			rightEvaluation = nodeFactory.newExpressionStatementNode(assign);
		}
		ifNode = nodeFactory.newIfNode(source, holderExpr.copy(),
				rightEvaluation);
		results.add(ifNode);
		return results;
	}

	private List<StatementNode> transformShortCircuitExpressionWorker_LOR(
			ExpressionNode left, ExpressionNode right, String holderName,
			Source source) {
		List<StatementNode> result;
		StatementNode rightEvaluation;
		ExpressionNode holderExpr = identifierExpression(holderName);
		IfNode ifNode;

		result = transformSCLeftOperand(left, holderName);
		rightEvaluation = transformSCRightOperand(right, holderName);

		if (rightEvaluation == null) {
			// If there is no SC operator in right expression, holder =
			// rightExpression;
			ExpressionNode assign = nodeFactory.newOperatorNode(
					right.getSource(), Operator.ASSIGN,
					Arrays.asList(holderExpr, right.copy()));

			rightEvaluation = nodeFactory.newExpressionStatementNode(assign);
		}
		ifNode = nodeFactory.newIfNode(
				source, nodeFactory.newOperatorNode(left.getSource(),
						Operator.NOT, Arrays.asList(holderExpr.copy())),
				rightEvaluation);
		result.add(ifNode);
		return result;

	}

	private List<StatementNode> transformShortCircuitExpressionWorker_IMPLIES(
			ExpressionNode left, ExpressionNode right, String holderName,
			Source source) {
		List<StatementNode> result;
		StatementNode rightEvaluation;
		ExpressionNode holderExpr = identifierExpression(holderName);
		ExpressionNode notHolder = nodeFactory.newOperatorNode(
				holderExpr.getSource(), Operator.NOT,
				Arrays.asList(holderExpr));
		IfNode ifNode;

		result = transformSCLeftOperand(left, holderName);
		rightEvaluation = transformSCRightOperand(right, holderName);

		result.add(nodeFactory.newExpressionStatementNode(
				nodeFactory.newOperatorNode(left.getSource(), Operator.ASSIGN,
						Arrays.asList(holderExpr.copy(), notHolder))));
		if (rightEvaluation == null) {
			// If there is no SC operator in right expression, holder =
			// rightExpression;
			ExpressionNode assign = nodeFactory.newOperatorNode(
					right.getSource(), Operator.ASSIGN,
					Arrays.asList(holderExpr.copy(), right.copy()));

			rightEvaluation = nodeFactory.newExpressionStatementNode(assign);
		}
		ifNode = nodeFactory.newIfNode(
				source, nodeFactory.newOperatorNode(left.getSource(),
						Operator.NOT, Arrays.asList(holderExpr.copy())),
				rightEvaluation);
		result.add(ifNode);
		return result;
	}

	private StatementNode transformSCRightOperand(ExpressionNode operand,
			String holderName) {
		Source source = operand.getSource();
		List<StatementNode> result = transformShortCircuitExpressionWorker(
				operand, holderName);
		StatementNode evaluation;

		if (result.isEmpty())
			return null;
		else if (result.size() == 1)
			evaluation = result.get(0);
		else {
			List<BlockItemNode> cast = new LinkedList<>();

			cast.addAll(result);
			evaluation = nodeFactory.newCompoundStatementNode(source, cast);
		}
		assert evaluation.blockItemKind() == BlockItemKind.STATEMENT;
		return evaluation;
	}

	private List<StatementNode> transformSCLeftOperand(ExpressionNode operand,
			String holderName) {
		Source source = operand.getSource();
		List<StatementNode> results = new LinkedList<>();

		results.addAll(
				transformShortCircuitExpressionWorker(operand, holderName));
		if (results.isEmpty()) {
			ExpressionNode holder = this.identifierExpression(holderName);
			ExpressionNode assignment = nodeFactory.newOperatorNode(source,
					Operator.ASSIGN, Arrays.asList(holder, operand.copy()));
			StatementNode initHolder = nodeFactory
					.newExpressionStatementNode(assignment);

			results.add(initHolder);
		}
		return results;
	}

	/* **************** Error side-effect over-approximation ******************/
	private boolean errorSideEffectOverapproximantion(
			ExpressionNode expression) {
		return false;
	}

	private boolean divByZeroOverapproximantion(ExpressionNode expression) {
		boolean divByZero = false;

		if (expression.expressionKind() == ExpressionKind.OPERATOR) {
			Operator oprt = ((OperatorNode) expression).getOperator();

			if (oprt == Operator.DIV || oprt == Operator.MOD) {
				ExpressionNode denominator = ((OperatorNode) expression)
						.getArgument(1);

				if (denominator.isConstantExpression()) {
					ConstantNode constant = (ConstantNode) denominator;

					divByZero = constant.getConstantValue()
							.isZero() != Answer.NO;
				}
			}
		}
		if (divByZero)
			return true;
		for (ASTNode node : expression.children())
			if (node.nodeKind() == NodeKind.EXPRESSION) {
				divByZero = divByZeroOverapproximantion((ExpressionNode) node);
				if (divByZero)
					return true;
			}
		return false;
	}

	private boolean pointerAdditionOverapproximation(
			ExpressionNode expression) {
		boolean pointerAddition = false;

		return false;
	}

	private boolean castOverapproximation(ExpressionNode expression) {
		boolean pointerAddition = false;

		return false;
	}

	private static boolean containsPointerAdd(ExpressionNode expression) {
		ExpressionKind kind = expression.expressionKind();

		switch (kind) {
			case ARROW :
				break;
			case OPERATOR :
				break;
			default :
				break;

		}
		return false;
	}
}
