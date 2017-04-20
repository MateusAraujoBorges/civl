package edu.udel.cis.vsl.civl.transform.common;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.OrdinaryDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.label.LabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.JumpNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.JumpNode.JumpKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode.LoopKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode.StatementKind;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;

public class LoopContractTransformerWorker extends BaseWorker {
	/**
	 * A reference to {@link NodeFactory}
	 */
	private NodeFactory nodeFactory;

	/* ************************ Static fields ****************************** */

	/* *** Function identifiers *** */
	private final static String ASSUME_PUSH = "$assume_push";

	private final static String ASSUME_POP = "$assume_pop";

	private final static String HAVOC_MEM = "$havoc_mem";

	private final static String WRITE_SET_PUSH = "$write_set_push";

	private final static String WRITE_SET_POP = "$write_set_pop";

	/* *** Type names *** */
	private final static String MEM_TYPE = "$mem";

	/* *** Generated identifier prefixes: *** */
	private final static String MEM_VAR_PREFIX = "_loop_mem_";

	private final static String CONTINUE_LABEL = "_LOOP_CONTINUE";

	/* *** Generated identifier counters *** */
	private int memCounter = 0;

	private int loopContinueCounter = 0;

	/* ******************** static methods ********************** */
	/**
	 * @param node
	 *            An {@link ASTNode}.
	 * @return true iff the given {@link ASTNode} represents a function
	 *         definition.
	 */
	static private boolean isFunctionDefinition(ASTNode node) {
		return node.nodeKind() == NodeKind.FUNCTION_DEFINITION;
	}

	/**
	 * @param node
	 *            An {@link ASTNode}.
	 * @return true iff the given {@link ASTNode} represents a loop.
	 */
	static private boolean isLoopNode(ASTNode node) {
		if (node.nodeKind() == NodeKind.STATEMENT)
			return ((StatementNode) node).statementKind() == StatementKind.LOOP;
		return false;
	}

	/**
	 * @param node
	 *            An {@link LoopNode}.
	 * @return true iff the given {@link LoopNode} represents a loop.
	 */
	static private boolean isContractedLoop(LoopNode loop) {
		return loop.loopContracts() != null
				&& loop.loopContracts().numChildren() > 0;
	}

	/**
	 * @param loop
	 *            An {@link LoopNode}.
	 * @return true iff the given {@link LoopNode} represents a for-loop.
	 */
	static private boolean isForLoop(LoopNode loop) {
		return loop.getKind() == LoopKind.FOR;
	}

	/**
	 * @param loop
	 *            An {@link LoopNode}.
	 * @return true iff the given {@link LoopNode} represents a do-while loop.
	 */
	static private boolean isDoWhileLoop(LoopNode loop) {
		return loop.getKind() == LoopKind.DO_WHILE;
	}

	/* ******************* Constructor ********************** */
	/**
	 * @return A unique identifier name for a $mem type object
	 */
	private String nextMenIdentifier() {
		return MEM_VAR_PREFIX + memCounter++;
	}

	/**
	 * @return A unique identifier name for a label which helps transforming
	 *         'continue's
	 */
	private String nextContinueLabelIdentifier() {
		return CONTINUE_LABEL + loopContinueCounter++;
	}

	/* ******************* Constructor ********************** */

	public LoopContractTransformerWorker(String transformerName,
			ASTFactory astFactory) {
		super(transformerName, astFactory);
		this.nodeFactory = astFactory.getNodeFactory();
	}

	/* ******************* The only public interface ********************** */
	@Override
	public AST transform(AST ast) throws SyntaxException {
		SequenceNode<BlockItemNode> root = ast.getRootNode();

		ast.release();
		for (BlockItemNode block : root) {
			if (isFunctionDefinition(block)) {
				FunctionDefinitionNode funcDefi = (FunctionDefinitionNode) block;

				transformLoopInFunction(funcDefi.getBody());
			}
		}
		completeSources(root);
		ast = astFactory.newAST(root, ast.getSourceFiles(),
				ast.isWholeProgram());
		ast.prettyPrint(System.out, false);
		return ast;
	}

	/* **************** Main transformation logic methods ****************** */
	/**
	 * Given a function body, transform all contracted loops in it into CIVL IR.
	 * 
	 * @param body
	 *            The root node of a sub-ASTree representing a function body
	 */
	private void transformLoopInFunction(BlockItemNode body) {
		ASTNode node = body;
		LoopContractBlock annotatedLoop;
		ASTNode parent = body.parent();
		int bodyChildIdx = body.childIndex();

		// temporarily take off the body so that the DFS will only traverse the
		// body:
		body.remove();
		do {
			// transform nested function definitions:
			if (isFunctionDefinition(node))
				transformLoopInFunction(
						((FunctionDefinitionNode) node).getBody());
			// transform loop:
			if (isLoopNode(node)) {
				LoopNode loop = (LoopNode) node;

				if (isContractedLoop(loop)) {
					// transform the loop
					annotatedLoop = new LoopContractBlock(loop);
					// skip the whole loop then continue. The loopNode will be
					// removed in transformLoopWorker method, so the Skip call
					// must happen before it.
					node = BaseWorker.nextDFSSkip(loop);
					transformLoopWorker(annotatedLoop);
					continue;
				}
			}
			node = node.nextDFS();
		} while (node != null);
		parent.setChild(bodyChildIdx, body);
	}

	/**
	 * Transform a contracted loop including nested ones into a sequence of CIVL
	 * IRs.
	 * 
	 * @param loop
	 */
	private void transformLoopWorker(LoopContractBlock loop) {
		// transfrom inner loops
		transformLoopInFunction(loop.getLoopNode().getBody());

		List<BlockItemNode> LISEComponents;
		String memVariableName = nextMenIdentifier();
		Source source = loop.getLoopNode().getSource();
		ASTNode loopParent = loop.getLoopNode().parent();
		BlockItemNode LISEBlock;
		LoopNode newLoop;
		int childIdx = loop.getLoopNode().childIndex();

		// adds auxillary statements before entering the loop:
		LISEComponents = transformLoopEntrance(loop, memVariableName);
		// transforms loop body:
		transformLoopBody(loop, memVariableName);
		// transforms the loop to a while(true) loop using 'break's to
		// terminate:
		newLoop = toWhileLoop(loop, memVariableName);
		// completes the while loop transformation by adding the very first
		// condition test if the loop is NOT a do-while loop:
		// "if (loop condition) while(true)-loop;"
		if (!isDoWhileLoop(loop.getLoopNode()))
			LISEComponents.add(nodeFactory.newIfNode(source,
					loop.getLoopNode().getCondition().copy(), newLoop));
		// transforms termination of a loop:
		LISEComponents.addAll(transformLoopExit(loop));
		LISEBlock = nodeFactory.newCompoundStatementNode(source,
				LISEComponents);
		loop.getLoopNode().remove();
		loopParent.setChild(childIdx, LISEBlock);
	}

	/* **************** Loop transformation helper methods ****************** */
	// TODO: Note that side-effects in for-loop initializers will happen before
	// the evaluation of loop invariants of the base case.
	/**
	 * Adding a sequence of statements before the entry of the loop:
	 * <li><b>A declaration of a unique variable of $mem type;</b>, which will
	 * be used to hold the write set during the execution of the loop body;</li>
	 * <li><b>loop initializers; (oprtional)</b>, which comes from for-loop
	 * initializers;</li>
	 * <li><b>An assertion checks if the loop invariants hold;</b>, which is
	 * part of the induction procedures: check if the base case holds;<br>
	 * </li> <br>
	 * 
	 * @param loop
	 * @param memVariableName
	 * @return A list of {@link BlockItemNode}s which should be put before the
	 *         loop entry.
	 */
	private List<BlockItemNode> transformLoopEntrance(LoopContractBlock loop,
			String memVariableName) {
		List<BlockItemNode> results = new LinkedList<>();
		Source source = loop.getLoopNode().getSource();

		// $mem type variable declaration:
		IdentifierNode memVarIdentifier = identifier(memVariableName);
		TypeNode memTypeNode = nodeFactory
				.newTypedefNameNode(identifier(MEM_TYPE), null);

		results.add(nodeFactory.newVariableDeclarationNode(source,
				memVarIdentifier, memTypeNode));
		// loop initializer:
		if (isForLoop(loop.getLoopNode())) {
			ForLoopNode forLoop = (ForLoopNode) loop.getLoopNode();
			ForLoopInitializerNode initializer = forLoop.getInitializer();

			if (initializer != null) {
				initializer.remove();
				if (initializer instanceof ExpressionNode)
					results.add(nodeFactory.newExpressionStatementNode(
							(ExpressionNode) initializer));
				else
					results.add((OrdinaryDeclarationNode) initializer);
			}
		}
		// base case assertion:
		results.add(createAssertion(loop.getLoopInvariants(nodeFactory)));
		return results;
	}

	/**
	 * Transform the loop body following the basic idea of "loop invariant
	 * symbolic execution" (LISE):<code>
	 *   Assumes (Push assume) the loop invariants hold; <br>
	 *   START_MONITORING_WRITE_SET <br>
	 *   Executes the loop body; <br>
	 *   CONTINUE_TARGET_LABEL: Increments loop identifiers (if it is a for-loop);
	 * <br>
	 *   Asserts the loop invariants still hold; <br>
	 *   END_MONITORING_WRITE_SET <br>
	 *   Refresh write set;<br>
	 *   (Pop assume); <br>
	 * </code>
	 * 
	 * @param loop
	 * @param memVariableName
	 * @return a set of {@link LoopJumperReplacers} for all loop jumpers belong
	 *         to this loop body (Not include ones in nested loops).
	 */
	private void transformLoopBody(LoopContractBlock loop,
			String memVariableName) {
		List<BlockItemNode> results = new LinkedList<>();
		StatementNode body = loop.getLoopNode().getBody();
		// The destination where continue jumpers will direct to:
		StatementNode continueJumperTarget = null;
		Source source = loop.getLoopNode().getBody().getSource();
		String continueLabelName = nextContinueLabelIdentifier();
		ASTNode parent = body.parent();
		int childIdx = body.childIndex();
		ExpressionNode loopInvariantsAndCondition = nodeFactory.newOperatorNode(
				source, Operator.LAND,
				Arrays.asList(loop.getLoopInvariants(nodeFactory),
						loop.getLoopNode().getCondition().copy()));

		body.remove();
		// Push assumptions:
		results.add(createAssumptionPush(loopInvariantsAndCondition));
		// START_MONITORING
		results.add(createWriteSetPush(source));
		// Process loop jumpers in the loop body:
		transformLoopJumpers(loop, body, memVariableName, continueLabelName);
		results.add(body);

		// Where the continue jumper destination locates:
		IdentifierNode continueJumperLabelIdentifier = identifier(
				continueLabelName);
		LabelNode continueJumperTargetLabel;

		// Adds incrementors:
		if (loop.getLoopNode().getKind() == LoopKind.FOR) {
			ForLoopNode forLoop = (ForLoopNode) loop.getLoopNode();

			if (forLoop.getIncrementer() != null) {
				continueJumperTarget = nodeFactory.newExpressionStatementNode(
						forLoop.getIncrementer().copy());
				continueJumperTargetLabel = nodeFactory
						.newStandardLabelDeclarationNode(source,
								continueJumperLabelIdentifier,
								continueJumperTarget);
				results.add(nodeFactory.newLabeledStatementNode(source,
						continueJumperTargetLabel, continueJumperTarget));
			}
		}
		// Asserts loop invariants:
		if (continueJumperTarget == null) {
			continueJumperTarget = createAssertion(
					loop.getLoopInvariants(nodeFactory));
			continueJumperTargetLabel = nodeFactory
					.newStandardLabelDeclarationNode(source,
							continueJumperLabelIdentifier,
							continueJumperTarget);
			results.add(nodeFactory.newLabeledStatementNode(source,
					continueJumperTargetLabel, continueJumperTarget));
		} else
			results.add(createAssertion(loop.getLoopInvariants(nodeFactory)));

		StatementNode newBody = nodeFactory.newCompoundStatementNode(source,
				results);

		parent.setChild(childIdx, newBody);
	}

	/**
	 * Convert a loop to a <code>while($true)</code> loop: <code>
	 * 
	 * while ($true) {
	 *    body;
	 *    if (!loop_condition) {
	 *       pop_write_set(&m);
	 *       $havoc_mem(m);
	 *       pop_assume();
	 *       break;
	 *    }
	 *    pop_write_set(&m);
	 *    $havoc_mem(m);
	 *    pop_assume();
	 * }
	 * 
	 * </code>
	 * 
	 * @param loop
	 * @return the new "while($true)" loop node.
	 */
	private LoopNode toWhileLoop(LoopContractBlock loop,
			String memVariableName) {
		List<BlockItemNode> results = new LinkedList<>();
		List<BlockItemNode> termination = new LinkedList<>();
		Source source = loop.getLoopNode().getSource();
		StatementNode body = loop.getLoopNode().getBody();

		body.remove();
		// Optimization, try to minimize the number of useless bracekets:
		if (body instanceof CompoundStatementNode) {
			CompoundStatementNode compoundBody = (CompoundStatementNode) body;

			for (BlockItemNode stmt : compoundBody) {
				stmt.remove();
				results.add(stmt);
			}
		} else
			results.add(body);
		// Add loop termination branch:
		// END_MONITORING:
		termination.add(createWriteSetPop(source, memVariableName));
		// Refresh write set:
		termination.add(createHavocMemCall(source, memVariableName));
		// Pops assumption:
		termination.add(createAssumptionPop(source));
		// Break;
		termination.add(nodeFactory.newBreakNode(source));

		ExpressionNode loopCondition = loop.getLoopNode().getCondition().copy();
		ExpressionNode notLoopCondition = nodeFactory.newOperatorNode(source,
				Operator.NOT, loopCondition);
		StatementNode terminationBranch = nodeFactory.newIfNode(source,
				notLoopCondition,
				nodeFactory.newCompoundStatementNode(source, termination));

		results.add(terminationBranch);
		// END_MONITORING:
		results.add(createWriteSetPop(source, memVariableName));
		// Refresh write set:
		results.add(createHavocMemCall(source, memVariableName));
		// Pops assumption:
		results.add(createAssumptionPop(source));

		StatementNode newBody = nodeFactory.newCompoundStatementNode(source,
				results);
		LoopNode newLoop = nodeFactory.newWhileLoopNode(source,
				nodeFactory.newBooleanConstantNode(source, true), newBody,
				null);

		return newLoop;
	}

	/**
	 * An exit of the LISE of a loop is mainly inferring the loop invariants
	 * hold and loop terminates:
	 * <code>$assume( !loop-condition && loop-invariants)</code>
	 * 
	 * @param block
	 * @return A list of {@link BlockItemNode} which should be appended after
	 *         the termination of the loop.
	 */
	private List<BlockItemNode> transformLoopExit(LoopContractBlock loop) {
		Source source = loop.getLoopNode().getCondition().getSource();
		ExpressionNode notLoopCondition = nodeFactory.newOperatorNode(source,
				Operator.NOT, loop.getLoopNode().getCondition().copy());
		ExpressionNode finalAssumption = nodeFactory.newOperatorNode(source,
				Operator.LAND, Arrays.asList(
						loop.getLoopInvariants(nodeFactory), notLoopCondition));
		StatementNode finalAssume = createAssumption(finalAssumption);

		return Arrays.asList(finalAssume);
	}

	/**
	 * Transform loop jumpers belong the given loop body.
	 * 
	 * @param body
	 * @param memVariableName
	 * @return
	 */
	private void transformLoopJumpers(LoopContractBlock loop,
			StatementNode body, String memVariableName,
			String continueLabelName) {
		ASTNode node = body;

		while (node != null) {
			if (node.nodeKind() == NodeKind.STATEMENT) {
				StatementNode stmtNode = (StatementNode) node;

				if (stmtNode.statementKind() == StatementKind.JUMP) {
					JumpNode jump = (JumpNode) stmtNode;
					JumpKind jumpKind = jump.getKind();

					switch (jumpKind) {
						case BREAK :
							transformLoopBreakWorker(loop, jump,
									memVariableName);
							break;
						case CONTINUE :
							transformLoopContinueWorker(loop, jump,
									memVariableName, continueLabelName);
							break;
						case RETURN :
							transformLoopReturnWorker(loop, jump,
									memVariableName);
							break;
						default :
							throw new CIVLUnimplementedFeatureException(
									"Transform loop jumper of kind: "
											+ jumpKind);
					}
				}
				// Skip nested loops:
				if (stmtNode.statementKind() == StatementKind.LOOP) {
					node = BaseWorker.nextDFSSkip(node);
					continue;
				}
			}
			node = node.nextDFS();
		}
	}

	/**
	 * Trasform a BREAK statement belonging to the loop:<code>
	 * 
	 * 
	 *   original_break_stmt ==>   { $assert(loop_invariants);
	 *                               $pop_write_set(&m); 
	 *                               $havoc_mem(m);
	 *                               $pop_assume();
	 *                               original_break_stmt;
	 *                              }
	 * 
	 * </code>
	 * 
	 * @param loop
	 * @param breakJumper
	 * @param memVariableName
	 */
	private void transformLoopBreakWorker(LoopContractBlock loop,
			JumpNode breakJumper, String memVariableName) {
		ASTNode parent = breakJumper.parent();
		int childIdx = breakJumper.childIndex();
		List<BlockItemNode> results = new LinkedList<>();
		Source source = breakJumper.getSource();

		// Asserts loop invariants:
		results.add(createAssertion(loop.getLoopInvariants(nodeFactory)));
		// END_MONITORING:
		results.add(createWriteSetPop(source, memVariableName));
		// Refresh write set:
		results.add(createHavocMemCall(source, memVariableName));
		// Pops assumption:
		results.add(createAssumptionPop(source));
		// Append the break jumper:
		breakJumper.remove();
		results.add(breakJumper);
		if (parent.nodeKind() == NodeKind.SEQUENCE) {
			@SuppressWarnings("unchecked")
			SequenceNode<BlockItemNode> sequence = (SequenceNode<BlockItemNode>) parent;

			sequence.insertChildren(childIdx, results);
		} else {
			StatementNode newCompoundNode = nodeFactory
					.newCompoundStatementNode(source, results);

			parent.setChild(childIdx, newCompoundNode);
		}
	}

	/**
	 * Transform a CONTINUE statement belonging to the loop: <code>
	 *  orginal continue stmt; ==> GOTO continue_target_label;
	 * </code> The "continue_target_label" locates immediately before the loop
	 * incrementor position (if the loop has incrememtor, it will be put at the
	 * position.).
	 * 
	 * @param loop
	 * @param continueJumper
	 * @param memVariableName
	 * @param labelName
	 */
	private void transformLoopContinueWorker(LoopContractBlock loop,
			JumpNode continueJumper, String memVariableName, String labelName) {
		ASTNode parent = continueJumper.parent();
		int childIdx = continueJumper.childIndex();
		BlockItemNode gotoStmt;
		Source source = continueJumper.getSource();
		IdentifierNode labelIdentifier = identifier(labelName);

		// Replace CONTINUE with GOTO:
		continueJumper.remove();
		gotoStmt = nodeFactory.newGotoNode(source, labelIdentifier);
		parent.setChild(childIdx, gotoStmt);
	}

	/**
	 * Transform a RETURN statement in a loop body: <code>
	 *  
	 *   original_return_stmt ==>  { $assert(loop_invariants);
	 *                               $pop_write_set(&m); 
	 *                               $havoc_mem(m);
	 *                               $pop_assume();
	 *                               $assume(loop_invariants);
	 *                               original_return_stmt;
	 *                              }
	 * </code>
	 * 
	 * @param loop
	 * @param returnJumper
	 * @param memVariableName
	 */
	private void transformLoopReturnWorker(LoopContractBlock loop,
			JumpNode returnJumper, String memVariableName) {
		ASTNode parent = returnJumper.parent();
		int childIdx = returnJumper.childIndex();
		List<BlockItemNode> results = new LinkedList<>();
		Source source = returnJumper.getSource();

		// Asserts loop invariants:
		results.add(createAssertion(loop.getLoopInvariants(nodeFactory)));
		// END_MONITORING:
		results.add(createWriteSetPop(source, memVariableName));
		// Refresh write set:
		results.add(createHavocMemCall(source, memVariableName));
		// Pops assumption:
		results.add(createAssumptionPop(source));
		// Add final assumption:
		results.add(createAssumption(loop.getLoopInvariants(nodeFactory)));
		// Append the return jumper:
		returnJumper.remove();
		results.add(returnJumper);
		if (parent.nodeKind() == NodeKind.SEQUENCE) {
			@SuppressWarnings("unchecked")
			SequenceNode<BlockItemNode> sequence = (SequenceNode<BlockItemNode>) parent;

			sequence.insertChildren(childIdx, results);
		} else {
			StatementNode newCompoundNode = nodeFactory
					.newCompoundStatementNode(source, results);

			parent.setChild(childIdx, newCompoundNode);
		}
	}

	/* *********************** Utility methods ****************************** */
	/**
	 * Creates an assertion function call with an argument "predicate".
	 * 
	 * @param predicate
	 *            The {@link ExpressionNode} which represents a predicate. It is
	 *            the only argument of an assertion call.
	 * @return A created assert call statement node;
	 */
	private StatementNode createAssertion(ExpressionNode predicate) {
		ExpressionNode assertIdentifier = identifierExpression(
				BaseWorker.ASSERT);
		FunctionCallNode assumeCall = nodeFactory.newFunctionCallNode(
				predicate.getSource(), assertIdentifier,
				Arrays.asList(predicate.copy()), null);
		return nodeFactory.newExpressionStatementNode(assumeCall);
	}

	/**
	 * Creates an assumption function call with an argument "predicate".
	 * 
	 * @param predicate
	 *            The {@link ExpressionNode} which represents a predicate. It is
	 *            the only argument of an assumption call.
	 * @return A created assumption call statement node;
	 */
	private StatementNode createAssumption(ExpressionNode predicate) {
		ExpressionNode assumeIdentifier = identifierExpression(
				BaseWorker.ASSUME);
		FunctionCallNode assumeCall = nodeFactory.newFunctionCallNode(
				predicate.getSource(), assumeIdentifier,
				Arrays.asList(predicate.copy()), null);
		return nodeFactory.newExpressionStatementNode(assumeCall);
	}

	/**
	 * Creates an assume_push function call with an argument "predicate".
	 * 
	 * @param predicate
	 *            The {@link ExpressionNode} which represents a predicate. It is
	 *            the only argument of an assumption call.
	 * @return A created assumption call statement node;
	 */
	private StatementNode createAssumptionPush(ExpressionNode predicate) {
		ExpressionNode assumeIdentifier = identifierExpression(ASSUME_PUSH);
		FunctionCallNode assumeCall = nodeFactory.newFunctionCallNode(
				predicate.getSource(), assumeIdentifier,
				Arrays.asList(predicate.copy()), null);
		return nodeFactory.newExpressionStatementNode(assumeCall);
	}

	/**
	 * Creates an assume_pop function call.
	 * 
	 * @return A created assumption call statement node;
	 */
	private StatementNode createAssumptionPop(Source source) {
		ExpressionNode assumeIdentifier = identifierExpression(ASSUME_POP);

		FunctionCallNode assumeCall = nodeFactory.newFunctionCallNode(source,
				assumeIdentifier, Arrays.asList(), null);
		return nodeFactory.newExpressionStatementNode(assumeCall);
	}

	/**
	 * Creates a write_set_push function call.
	 * 
	 * @return A created write set push statement node;
	 */
	private StatementNode createWriteSetPush(Source source) {
		ExpressionNode wsPushIdentifier = identifierExpression(WRITE_SET_PUSH);
		FunctionCallNode wsPushCall = nodeFactory.newFunctionCallNode(source,
				wsPushIdentifier, Arrays.asList(), null);
		return nodeFactory.newExpressionStatementNode(wsPushCall);
	}

	/**
	 * Creates a write_set_pop($mem * m) function call.
	 * 
	 * @return A created write set pop statement node;
	 */
	private StatementNode createWriteSetPop(Source source, String memVarName) {
		IdentifierNode memVarIdentifier = identifier(memVarName);
		ExpressionNode memVar = nodeFactory.newIdentifierExpressionNode(source,
				memVarIdentifier);
		ExpressionNode addressofMemVar = nodeFactory.newOperatorNode(source,
				Operator.ADDRESSOF, Arrays.asList(memVar));
		ExpressionNode wsPopIdentifier = identifierExpression(WRITE_SET_POP);

		FunctionCallNode wsPopCall = nodeFactory.newFunctionCallNode(source,
				wsPopIdentifier, Arrays.asList(addressofMemVar), null);
		return nodeFactory.newExpressionStatementNode(wsPopCall);
	}

	/**
	 * Creates an $havoc_mem($mem m) function call:
	 * 
	 * @param var
	 *            An {@link ExpressionNode} representing an variable.
	 * @return The created $havoc call expression node.
	 */
	private BlockItemNode createHavocMemCall(Source source, String memVarName) {
		IdentifierNode memVarIdentifier = identifier(memVarName);
		ExpressionNode callIdentifier = identifierExpression(HAVOC_MEM);
		ExpressionNode varExpression = nodeFactory
				.newIdentifierExpressionNode(source, memVarIdentifier);
		FunctionCallNode call = nodeFactory.newFunctionCallNode(source,
				callIdentifier, Arrays.asList(varExpression), null);

		return nodeFactory.newExpressionStatementNode(call);
	}
}
