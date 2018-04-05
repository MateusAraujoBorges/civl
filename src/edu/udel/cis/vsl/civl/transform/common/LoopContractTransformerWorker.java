package edu.udel.cis.vsl.civl.transform.common;

import java.io.File;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Variable;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StringLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.LabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.DeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.JumpNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.JumpNode.JumpKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode.LoopKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode.StatementKind;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.abc.front.IF.CivlcTokenConstant;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.Formation;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.StringLiteral;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.transform.common.contracts.MemoryLocationManager;
import edu.udel.cis.vsl.civl.transform.common.contracts.MemoryLocationManager.MemoryBlock;

public class LoopContractTransformerWorker extends BaseWorker {
	/**
	 * A reference to {@link NodeFactory}
	 */
	private NodeFactory nodeFactory;

	private final static String LOOP_ASSIGNS_AUTO_GEN_HEADER = "/include/abc/loop_assigns_gen.cvh";

	private final static String MEM_HEADER = "/include/abc/mem.cvh";

	private final static String LOOP_ASSIGNS_AUTO_GEN_IMPL = "/include/civl/loop_assigns_gen.cvl";

	private final static String MEM_IMPL = "/include/civl/mem.cvl";

	// private final static String STRING_HEADER = "/include/abc/string.h";

	// private final static String STRING_IMPL = "/include/civl/string.cvl";

	/* ************************ Static fields ****************************** */

	/* *** Function identifiers *** */
	private final static String ASSUME_PUSH = "$assume_push";

	private final static String ASSUME_POP = "$assume_pop";

	private final static String WRITE_SET_PUSH = "$write_set_push";

	private final static String WRITE_SET_POP = "$write_set_pop";

	private final static String WRITE_SET_PEEK = "$write_set_peek";

	private final static String REGULAR_GET_STATE_CALL = "$get_state";

	private final static String REGULAR_GET_FULL_STATE_CALL = "$get_full_state";

	private final static String LOOP_WRITE_SET_UNION = "$loop_write_set_union";

	private final static String LOOP_WRITE_SET_WIDENING = "$loop_write_set_widening";

	private final static String LOOP_WRITE_SET_HAVOC = "$loop_write_set_havoc";

	private final static String LOOP_WRITE_SET_NEW = "$loop_write_set_new";

	private final static String MEM_SIZE = "$mem_to_pointers_size";

	private final static String MEM_TO_POINTER_ARRAY = "$mem_to_pointers";

	/* *** Type names *** */
	private final static String LOOP_WRITE_SET_TYPE = "$loop_write_set";

	private final static String MEM_TYPE = "$mem";

	private final static String STATE_TYPE = "$state";

	/* *** Generated identifier prefixes: *** */
	/**
	 * A $loop_write_set object which is associated to a loop for collecting all
	 * modified memory locations.
	 */
	private final static String MEM_VAR_PREFIX = "_loop_mem_";

	/**
	 * A boolean value variable which is associated to a loop for holding
	 * assumptions that are generated during havoking of all modified locations.
	 */
	private final static String MEM_ASSUMPTION_VAR_PREFIX = "_loop_mem_assump";

	/**
	 * A $state type variable which is a reference to the pre-state of entering
	 * a loop.
	 */
	private final static String PRE_STATE_VAR_PREFIX = "_loop_pre_state";

	/**
	 * A boolean value variable which is associated to a loop and is the new
	 * loop condition of the loop after transformation. The new loop condition
	 * is the short-circuit disjunction of the least number of iteration
	 * execution condition and the simple non-deterministic choice between true
	 * and false.
	 */
	private final static String LOOP_NEW_COND_PREFIX = "_loop_new_cond";

	/**
	 * An integral variable which counts the number of iterations. This variable
	 * is used to force the control will never exit the loop until it executes
	 * the loop for at least some iterations once it enters the loop. This is
	 * idea is for 1) collecting more modified memory locations before widening;
	 * 2) reduce the number of states by reducing the states that are the
	 * results of exiting the loop before converge.
	 */
	private final static String LEAST_ITERS_PREFIX = "_loop_least_iters";

	/**
	 * Names for miscellaneous temporary variables that do not need to be passed
	 * among different methods.
	 */
	private final static String LOOP_TMP_VAR_PREFIX = "_loop_tmp";

	/**
	 * A label for translating <code>continue</code> to <code>goto</code>.
	 */
	private final static String CONTINUE_LABEL = "_LOOP_CONTINUE";

	/* *** counters for generating unique identifiers *** */

	private int memCounter = 0;

	private int memAssumpCounter = 0;

	private int loopPreStateCounter = 0;

	private int loopNewCondCounter = 0;

	private int loopLeastItersCounter = 0;

	private int loopTmpCounter = 0;

	private int loopContinueCounter = 0;

	/* ********** Widening heuristic conditions ***********/
	/**
	 * The least number of iterations the program will execute to collect enough
	 * write set samples.
	 */
	private final ExpressionNode LEAST_NUM_ITERATIONS;

	/* ************** primitives for error reporting **************** */

	/**
	 * The token used to construct a {@link StringLiteral} which is used to
	 * report assertion violation.
	 */
	private final CivlcToken loopInvariantsViolationMessageToken;

	/**
	 * The static string literal of loop invariants violation messages
	 */
	private static final String violationMessage = "\"loop invariants violation\"";

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
	 * @return A unique identifier name for a $loop_write_set type object
	 */
	private String nextMenIdentifier() {
		return MEM_VAR_PREFIX + memCounter++;
	}

	/**
	 * @return A unique identifier name for a boolean value assumption variable.
	 */
	private String nextMenAssumpIdentifier() {
		return MEM_ASSUMPTION_VAR_PREFIX + memAssumpCounter++;
	}

	/**
	 * @return A unique identifier name for a variable referencing the pre-state
	 */
	private String nextLoopPreStateIdentifier() {
		return PRE_STATE_VAR_PREFIX + loopPreStateCounter++;
	}

	/**
	 * @return A unique identifier name for a new loop condition variable
	 */
	private String nextLoopNewCondIdentifier() {
		return LOOP_NEW_COND_PREFIX + loopNewCondCounter++;
	}

	/**
	 * @return A unique identifier name for a counter variable which counts the
	 *         number of executed iterations.
	 */
	private String nextLoopLeastItersIdentifier() {
		return LEAST_ITERS_PREFIX + loopLeastItersCounter++;
	}

	/**
	 * @return A unique identifier name for miscellaneous variables which are
	 *         only used by within one Java method.
	 */
	private String nextLoopTmpIdentifier() {
		return LOOP_TMP_VAR_PREFIX + loopTmpCounter++;
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
			ASTFactory astFactory) throws SyntaxException {
		super(transformerName, astFactory);
		this.nodeFactory = astFactory.getNodeFactory();
		Formation feedBackformation = tokenFactory
				.newTransformFormation(transformerName, "violation report");
		Formation wideningConditionFormation = tokenFactory
				.newTransformFormation(transformerName, "widening condition");
		CivlcToken wideningCondToken = tokenFactory.newCivlcToken(
				CivlcTokenConstant.INTEGER_CONSTANT, "2",
				wideningConditionFormation);

		loopInvariantsViolationMessageToken = tokenFactory.newCivlcToken(
				CivlcTokenConstant.STRING_LITERAL, violationMessage,
				feedBackformation);
		LEAST_NUM_ITERATIONS = nodeFactory.newIntegerConstantNode(
				tokenFactory.newSource(wideningCondToken), "2");
	}

	/* ******************* The only public interface ********************** */
	@Override
	public AST transform(AST ast) throws SyntaxException {
		SequenceNode<BlockItemNode> root = ast.getRootNode();
		boolean hasContractedLoop = false;

		ast.release();
		for (BlockItemNode block : root) {
			if (isFunctionDefinition(block)) {
				FunctionDefinitionNode funcDefi = (FunctionDefinitionNode) block;

				if (transformLoopInFunction(funcDefi.getBody()))
					hasContractedLoop = true;
			}
		}

		if (!hasContractedLoop)
			return astFactory.newAST(root, ast.getSourceFiles(),
					ast.isWholeProgram());;

		root.insertChildren(0, addLibrary(LOOP_ASSIGNS_AUTO_GEN_IMPL));
		root.insertChildren(0, addLibrary(MEM_IMPL));
		root.insertChildren(0, addLibrary(LOOP_ASSIGNS_AUTO_GEN_HEADER));
		root.insertChildren(0, addLibrary(MEM_HEADER));
		completeSources(root);
		ast = astFactory.newAST(root, ast.getSourceFiles(),
				ast.isWholeProgram());
		ast.prettyPrint(System.out, true);
		return ast;
	}

	/**
	 * Adds an library AST to the given AST
	 * 
	 * @param filePath
	 * @return
	 */
	private List<BlockItemNode> addLibrary(String filePath) {
		try {
			AST ast = astFactory.getASTofLibrary(new File(filePath),
					Language.CIVL_C);
			SequenceNode<BlockItemNode> root = ast.getRootNode();
			List<BlockItemNode> result = new LinkedList<>();

			ast.release();
			for (BlockItemNode node : root) {
				node.remove();
				result.add(node);
			}
			return result;
		} catch (ABCException e) {
			throw new CIVLSyntaxException(
					"Unexpected error happens during parsing library: "
							+ filePath + "\n" + e.getMessage());
		}
	}

	/* **************** Main transformation logic methods ****************** */
	/**
	 * Given a function body, transform all contracted loops in it into CIVL-C
	 * codes.
	 * 
	 * @param body
	 *            The root node of a sub-ASTree representing a function body
	 * @return true iff at least one loop in this function has been annotated
	 * @throws SyntaxException
	 */
	private boolean transformLoopInFunction(BlockItemNode body)
			throws SyntaxException {
		ASTNode node = body;
		LoopContractBlock annotatedLoop;
		ASTNode parent = body.parent();
		int bodyChildIdx = body.childIndex();
		boolean hasContractedLoop = false;

		// temporarily take off the body so that the DFS will only traverse the
		// body:
		body.remove();
		do {
			// transform nested function definitions:
			if (isFunctionDefinition(node)) {
				boolean innerHasContractedLoop = transformLoopInFunction(
						((FunctionDefinitionNode) node).getBody());

				if (innerHasContractedLoop)
					hasContractedLoop = true;
			}
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
					hasContractedLoop = true;
					continue;
				}
			}
			node = node.nextDFS();
		} while (node != null);
		parent.setChild(bodyChildIdx, body);
		return hasContractedLoop;
	}

	/**
	 * Transform a contracted loop including nested ones into a sequence of
	 * CIVL-C codes.
	 * 
	 * @param loop
	 * @throws SyntaxException
	 */
	private void transformLoopWorker(LoopContractBlock loop)
			throws SyntaxException {
		// transfrom inner loops
		transformLoopInFunction(loop.getLoopNode().getBody());

		List<BlockItemNode> LISEComponents;
		// Create names for all auxiliary variables that will be used in the
		// loop transformation:
		AuxiliaryVariableNames auxVarNames = new AuxiliaryVariableNames(
				nextMenIdentifier(), nextMenAssumpIdentifier(),
				nextLoopPreStateIdentifier(), nextLoopNewCondIdentifier(),
				nextLoopLeastItersIdentifier());
		Source source = loop.getLoopNode().getSource();
		ASTNode loopParent = loop.getLoopNode().parent();
		BlockItemNode LISEBlock;
		LoopNode newLoop;
		int childIdx = loop.getLoopNode().childIndex();

		// adds statements for auxiliary variables before entering the loop:
		LISEComponents = transformLoopEntrance(loop, auxVarNames);
		// transforms loop body:
		transformLoopBody(loop, auxVarNames);
		// transforms the loop to a while(true) loop using 'break's to
		// terminate:
		newLoop = toWhileLoop(loop, auxVarNames);
		// completes the while loop transformation by adding the very first
		// condition test if the loop is NOT a do-while loop:
		// "if (loop condition) while(true)-loop;"
		if (!isDoWhileLoop(loop.getLoopNode()))
			LISEComponents.add(nodeFactory.newIfNode(source,
					loop.getLoopNode().getCondition().copy(), newLoop));
		// transforms termination of a loop:
		LISEComponents.addAll(transformLoopExit(loop, auxVarNames));
		LISEBlock = nodeFactory.newCompoundStatementNode(source,
				LISEComponents);
		loop.getLoopNode().remove();
		loopParent.setChild(childIdx, LISEBlock);
	}

	/* **************** Loop transformation helper methods ****************** */
	// TODO: Note that side-effects in for-loop initializers will happen before
	// the evaluation of loop invariants of the base case.
	/**
	 * Adding a sequence of statements before the entry of the loop: <br>
	 * <code>
	 * $loop_write_set mem = $loop_write_set_new();
	 * _Bool mem_assume = 1;
	 * _Bool new_loop_cond = 1;
	 * int least_iters_counter = 0;
	 * for-loop-initializer (optional)
	 * $assert(invariant);
	 * $state preState = $get_full_state();
	 * ...
	 * </code>
	 * 
	 * @param loop
	 * @param auxVarNames
	 *            all auxiliary variable names for this loop
	 * @return A list of {@link BlockItemNode}s which should be put before the
	 *         loop entry.
	 * @throws SyntaxException
	 */
	private List<BlockItemNode> transformLoopEntrance(LoopContractBlock loop,
			AuxiliaryVariableNames auxVarNames) throws SyntaxException {
		List<BlockItemNode> results = new LinkedList<>();
		Source source = loop.getLoopNode().getSource();
		// $loop_write_set type variable declaration:
		IdentifierNode memVarIdentifier = identifier(
				auxVarNames.loop_write_set);
		TypeNode memTypeNode = nodeFactory
				.newTypedefNameNode(identifier(LOOP_WRITE_SET_TYPE), null);
		// boolean type mem_assumption variable declaration
		IdentifierNode memAssumpVarIdentifier = identifier(
				auxVarNames.loop_mem_assumption);
		// boolean type loop termination condition variable declaration
		IdentifierNode loopNewCondIdentifier = identifier(
				auxVarNames.loop_new_cond);
		TypeNode boolTypeNode = nodeFactory.newBasicTypeNode(source,
				BasicTypeKind.BOOL);
		// integral type iteration counter variable declaration
		IdentifierNode loopLeastItersIdentifier = identifier(
				auxVarNames.loop_least_iters_counter);
		TypeNode intTypeNode = nodeFactory.newBasicTypeNode(source,
				BasicTypeKind.INT);

		results.add(
				nodeFactory.newVariableDeclarationNode(source, memVarIdentifier,
						memTypeNode, createNewLoopWriteSetCall(source)));
		results.add(nodeFactory.newVariableDeclarationNode(source,
				memAssumpVarIdentifier, boolTypeNode,
				nodeFactory.newIntegerConstantNode(source, "1")));
		results.add(nodeFactory.newVariableDeclarationNode(source,
				loopNewCondIdentifier, boolTypeNode.copy(),
				nodeFactory.newIntegerConstantNode(source, "1")));
		results.add(nodeFactory.newVariableDeclarationNode(source,
				loopLeastItersIdentifier, intTypeNode,
				nodeFactory.newIntegerConstantNode(source, "0")));
		// loop initializer:
		if (isForLoop(loop.getLoopNode())) {
			ForLoopNode forLoop = (ForLoopNode) loop.getLoopNode();
			ForLoopInitializerNode initializer = forLoop.getInitializer();

			if (initializer != null) {
				initializer.remove();
				if (initializer instanceof ExpressionNode)
					results.add(nodeFactory.newExpressionStatementNode(
							(ExpressionNode) initializer));
				else {
					DeclarationListNode declList = (DeclarationListNode) initializer;

					for (VariableDeclarationNode decl : declList) {
						decl.remove();
						results.add(decl);
					}
				}
			}
		}
		// base case assertion:
		results.add(createAssertion(loop.getLoopInvariants(nodeFactory)));

		// loop pre-state declaration :
		IdentifierNode preStateVarIdentifier = identifier(
				auxVarNames.loop_pre_state);
		TypeNode stateTypeNode = createStateTypeNode(source);
		ExpressionNode getStateCall = createGetStateCall(source,
				loop.getLoopAssignSet().isEmpty());

		results.add(nodeFactory.newVariableDeclarationNode(source,
				preStateVarIdentifier, stateTypeNode, getStateCall));
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
	 * @throws SyntaxException
	 */
	private void transformLoopBody(LoopContractBlock loop,
			AuxiliaryVariableNames auxVarNames) throws SyntaxException {
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
		results.add(
				createAssumptionPush(loopInvariantsAndCondition, auxVarNames));
		// Push write set (start monitoring):
		results.add(createWriteSetPush(source));
		// Process loop jumpers in the loop body:
		transformLoopJumpers(loop, body, auxVarNames, continueLabelName);
		results.add(body);

		// Where the continue jumper destination locates:
		IdentifierNode continueJumperLabelIdentifier = identifier(
				continueLabelName);
		LabelNode continueJumperTargetLabel;

		// Adds incrementers:
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
	 * while (loop_new_cond) {
	 *    body;
	 *    $loop_write_set_update(&loop_mem, $write_set_pop());
	 *    if (leastIters < N)
	 *      leastIters++;
	 *    loopNewCond = leastIters < N || $choose_int(2);
	 *    loop_assump = $loop_write_set_havoc(loop_mem);
	 *    pop_assume();
	 * }
	 * 
	 * </code>
	 * 
	 * @param loop
	 * @return the new "while($true)" loop node.
	 * @throws SyntaxException
	 */
	private LoopNode toWhileLoop(LoopContractBlock loop,
			AuxiliaryVariableNames auxVarNames) throws SyntaxException {
		List<BlockItemNode> results = new LinkedList<>();
		Source source = loop.getLoopNode().getSource();
		StatementNode body = loop.getLoopNode().getBody();

		body.remove();
		// Optimization, try to minimize the number of useless brackets:
		if (body instanceof CompoundStatementNode) {
			CompoundStatementNode compoundBody = (CompoundStatementNode) body;

			for (BlockItemNode stmt : compoundBody) {
				stmt.remove();
				results.add(stmt);
			}
		} else
			results.add(body);

		// // END_MONITORING:
		// results.addAll(writeSetPopAndUpdate(source, loop, auxVarNames));
		// // Updates new loop condition:
		// results.addAll(loopNewCondition(source, auxVarNames));
		// // Refresh write set:
		// results.add(createHavocMemCall(source, auxVarNames));
		results.addAll(transformLoopAssigns(loop, auxVarNames, false));
		// Pops assumption:
		results.add(createAssumptionPop(source));
		// ND choice of enter or exit:
		if (!loop.getLoopAssignSet().isEmpty())
			results.add(
					nodeFactory.newExpressionStatementNode(
							nodeFactory.newOperatorNode(source, Operator.ASSIGN,
									identifierExpression(
											auxVarNames.loop_new_cond),
									createNDBinaryChoice(source))));

		StatementNode newBody = nodeFactory.newCompoundStatementNode(source,
				results);
		LoopNode newLoop = nodeFactory.newWhileLoopNode(source,
				identifierExpression(auxVarNames.loop_new_cond), newBody, null);

		return newLoop;
	}

	private List<BlockItemNode> transformLoopAssigns(LoopContractBlock loop,
			AuxiliaryVariableNames auxVarNames, boolean isTermination)
			throws SyntaxException {
		// if loop has annotated "loop assigns" directly use loop assigns,
		// otherwise attempt to generate loop assigns using $mem object.
		if (loop.getLoopAssignSet().isEmpty())
			return loopAssignsGeneration(loop, auxVarNames, isTermination);
		else
			return transformLoopAssignsWorker(loop.getLoopAssignSet(),
					auxVarNames, loop.getLoopNode().getSource());
	}

	/**
	 * Enable the auto-determination of "loop assigns" mechanism. see the
	 * "loop_auto_gen.cvh" header.
	 */
	private List<BlockItemNode> loopAssignsGeneration(LoopContractBlock loop,
			AuxiliaryVariableNames auxVarNames, boolean isTermination)
			throws SyntaxException {
		Source source = loop.getLoopNode().getSource();
		// END_MONITORING:
		List<BlockItemNode> results = new LinkedList<>(
				writeSetPopAndUpdate(source, loop, auxVarNames));

		if (!isTermination)
			// Updates new loop condition:
			results.addAll(loopNewCondition(source, auxVarNames));
		// Refresh write set:
		results.add(createHavocMemCall(source, auxVarNames));
		return results;
	}

	/**
	 * Check write set is a subset of memory location set : <code>
	 * 
	 * $mem loop_tmp_ws = write_set_pop();
	 * int loop_tmp_length = mem_to_pointers_size(ws);
	 * if (loop_tmp_length > 0) {
	 *   void * _loop_tmp_ptrs[loop_tmp_length];
	 *   mem_to_pointers(loop_tmp_ws, &_loop_tmp_ptrs); 
	 *   foreach (ptr : _loop_tmp_ptrs);
	 *     $assert(EXISTS ptr in m);
	 * }
	 * </code><br>
	 * For each memory location set expression <code>m</code>, <code>
	 *   $havoc(&variable(m));
	 *   $assume(forall-unchanged-locations: m == old(m));
	 * </code>
	 * 
	 * @throws SyntaxException
	 */
	private List<BlockItemNode> transformLoopAssignsWorker(
			List<ExpressionNode> assignsArgs,
			AuxiliaryVariableNames auxVarNames, Source source)
			throws SyntaxException {
		List<BlockItemNode> results = new LinkedList<>();
		MemoryLocationManager memoryLocationManager = new MemoryLocationManager(
				nodeFactory);
		TypeNode memType = nodeFactory.newTypedefNameNode(identifier(MEM_TYPE),
				null);
		String ws_mem = nextLoopTmpIdentifier();

		// check if every element in write_set belongs to the "loop assigns"
		// set:
		results.add(nodeFactory.newVariableDeclarationNode(source,
				identifier(ws_mem), memType,
				functionCall(source, WRITE_SET_PEEK, Arrays.asList())));
		results.addAll(checkPointerBelongtoMemoryLocationSet(
				identifierExpression(ws_mem), assignsArgs, source,
				memoryLocationManager));
		// clear loop_mem_assumption
		results.add(nodeFactory.newExpressionStatementNode(
				nodeFactory.newOperatorNode(source, Operator.ASSIGN,
						identifierExpression(auxVarNames.loop_mem_assumption),
						nodeFactory.newIntegerConstantNode(source, "1"))));
		// havoc and assume for each "loop assigns" argument:
		for (ExpressionNode memLocSet : assignsArgs) {
			Variable variable = memoryLocationManager
					.variableContainingMemoryLocationSet(memLocSet);

			results.add(getRefreshStatements(source, variable, memLocSet,
					memoryLocationManager));
			results.add(createLogicalAndEquals(
					identifierExpression(auxVarNames.loop_mem_assumption),
					memoryLocationManager.refreshmentAssumptions(memLocSet,
							identifierExpression(auxVarNames.loop_pre_state),
							nodeFactory.newIntegerConstantNode(source, "0")),
					source));
		}
		results.add(nodeFactory.newExpressionStatementNode(
				functionCall(source, WRITE_SET_POP, Arrays.asList())));
		// TODO: using flush involves some problems due to lack of knowledge of
		// the assigned arguments dynamically.
		// results.add(nodeFactory.newExpressionStatementNode(functionCall(source,
		// WRITE_SET_FLUSH, Arrays.asList(identifierExpression(ws_mem)))));
		return results;
	}

	/**
	 * <p>
	 * Given a memSet expression <code>m</code>, if the variable
	 * <code>addrVar(m)</code> containing the base-address of <code>m</code> has
	 * non-pointer type, return <code>$havoc(&m)</code>. Else if
	 * <code>addrVar(m)</code> has a pointer-to-T type, where T is non-pointer
	 * and non-void, return <code>
	 * {
	 *   T[num_elements] tmp;
	 *   memcpy(addrVar(m), tmp, sizeof(T[num_elements]));
	 * } 
	 * </code>.
	 * </p>
	 */
	public BlockItemNode getRefreshStatements(Source source, Variable variable,
			ExpressionNode memLocSet,
			MemoryLocationManager memoryLocationManager)
			throws SyntaxException {
		if (variable.getType().kind() != TypeKind.POINTER) {
			ExpressionNode havocee = nodeFactory.newOperatorNode(source,
					Operator.ADDRESSOF,
					nodeFactory.newIdentifierExpressionNode(source, nodeFactory
							.newIdentifierNode(source, variable.getName())));

			return nodeFactory.newExpressionStatementNode(
					nodeFactory.newFunctionCallNode(source,
							nodeFactory.newIdentifierExpressionNode(source,
									nodeFactory.newIdentifierNode(source,
											BaseWorker.HAVOC)),
							Arrays.asList(havocee), null));
		} else {
			MemoryBlock memBlk = memoryLocationManager
					.getMemoryLocationSize(memLocSet);
			ExpressionNode memBlkSize = memBlk.count;

			if (memBlkSize == null)
				// refresh with $havoc directly:
				return nodeFactory.newExpressionStatementNode(
						nodeFactory.newFunctionCallNode(source,
								nodeFactory.newIdentifierExpressionNode(source,
										nodeFactory.newIdentifierNode(source,
												BaseWorker.HAVOC)),
								Arrays.asList(memBlk.baseAddress.copy()),
								null));

			// refresh a block slice:
			Type arrayOfReferredType = nodeFactory.typeFactory()
					.variableLengthArrayType((ObjectType) memBlk.type,
							memBlkSize);
			VariableDeclarationNode tempVarDecl = nodeFactory
					.newVariableDeclarationNode(source,
							nodeFactory.newIdentifierNode(source,
									nextLoopTmpIdentifier()),
							typeNode(arrayOfReferredType));
			// {
			// T[mem_size] tmp;
			// memcpy(mem-set-pointer-var, tmp, mem_size * sizeof(T));
			// }
			ExpressionNode byteWiseSize = nodeFactory.newSizeofNode(source,
					typeNode(arrayOfReferredType));
			BlockItemNode memcpyStmt = createMemcpyCall(source,
					identifierExpression(variable.getName()),
					identifierExpression(tempVarDecl.getIdentifier().name()),
					byteWiseSize);

			return nodeFactory.newCompoundStatementNode(source,
					Arrays.asList(tempVarDecl, memcpyStmt));
		}
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
	private List<BlockItemNode> transformLoopExit(LoopContractBlock loop,
			AuxiliaryVariableNames auxVarNames) {
		Source source = loop.getLoopNode().getCondition().getSource();
		ExpressionNode notLoopCondition = nodeFactory.newOperatorNode(source,
				Operator.NOT, loop.getLoopNode().getCondition().copy());
		ExpressionNode finalAssumption = nodeFactory.newOperatorNode(source,
				Operator.LAND, Arrays.asList(
						loop.getLoopInvariants(nodeFactory), notLoopCondition));
		StatementNode finalAssume = createLoopInvariantAssumption(
				finalAssumption, auxVarNames);

		return Arrays.asList(finalAssume);
	}

	/**
	 * Transform loop jumpers belong the given loop body.
	 * 
	 * @param body
	 * @param memVariableName
	 * @return
	 * @throws SyntaxException
	 */
	private void transformLoopJumpers(LoopContractBlock loop,
			StatementNode body, AuxiliaryVariableNames auxVarNames,
			String continueLabelName) throws SyntaxException {
		ASTNode node = body;

		while (node != null) {
			if (node.nodeKind() == NodeKind.STATEMENT) {
				StatementNode stmtNode = (StatementNode) node;

				if (stmtNode.statementKind() == StatementKind.JUMP) {
					JumpNode jump = (JumpNode) stmtNode;
					JumpKind jumpKind = jump.getKind();

					switch (jumpKind) {
						case BREAK :
							transformLoopBreakWorker(loop, jump, auxVarNames);
							break;
						case CONTINUE :
							transformLoopContinueWorker(loop, jump, auxVarNames,
									continueLabelName);
							break;
						case RETURN :
							transformLoopReturnWorker(loop, jump, auxVarNames);
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
	 *   original_break_stmt ==>   { 
	 *                               $loop_write_set_update(&loop_mem, $write_set_pop());
	 *                               loop_assump = $loop_write_set_havoc(loop_mem);
	 *                               pop_assume();
	 *                               break;
	 *                               //TODO: in this case, one cannot finally assume !loop-condition
	 *                              }
	 * 
	 * </code>
	 * 
	 * @param loop
	 * @param breakJumper
	 * @param memVariableName
	 * @throws SyntaxException
	 */
	private void transformLoopBreakWorker(LoopContractBlock loop,
			JumpNode breakJumper, AuxiliaryVariableNames auxVarNames)
			throws SyntaxException {
		ASTNode parent = breakJumper.parent();
		int childIdx = breakJumper.childIndex();
		List<BlockItemNode> results = new LinkedList<>();
		Source source = breakJumper.getSource();

		// Asserts loop invariants:
		results.add(createAssertion(loop.getLoopInvariants(nodeFactory)));
		// // END_MONITORING:
		// results.addAll(writeSetPopAndUpdate(source, loop, auxVarNames));
		// // Refresh write set:
		// results.add(createHavocMemCall(source, auxVarNames));
		results.addAll(transformLoopAssigns(loop, auxVarNames, true));
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
			JumpNode continueJumper, AuxiliaryVariableNames auxVarNames,
			String labelName) {
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
	 *   original_return_stmt ==>  { 
	 *                               $loop_write_set_update(&loop_mem, $write_set_pop());
	 *                               loop_assump = $loop_write_set_havoc(loop_mem);
	 *                               pop_assume();
	 *                               // notice that cannot assume the negation of the loop condition
	 *                               $assume(invariant && loop_assump); 
	 *                                original_return_stmt;
	 *                              }
	 * </code>
	 * 
	 * @param loop
	 * @param returnJumper
	 * @param memVariableName
	 * @throws SyntaxException
	 */
	private void transformLoopReturnWorker(LoopContractBlock loop,
			JumpNode returnJumper, AuxiliaryVariableNames auxVarNames)
			throws SyntaxException {
		ASTNode parent = returnJumper.parent();
		int childIdx = returnJumper.childIndex();
		List<BlockItemNode> results = new LinkedList<>();
		Source source = returnJumper.getSource();

		// Asserts loop invariants:
		results.add(createAssertion(loop.getLoopInvariants(nodeFactory)));
		// // END_MONITORING:
		// results.addAll(writeSetPopAndUpdate(source, loop, auxVarNames));
		// // Refresh write set:
		// results.add(createHavocMemCall(source, auxVarNames));
		results.addAll(transformLoopAssigns(loop, auxVarNames, true));
		// Pops assumption:
		results.add(createAssumptionPop(source));
		// Add final havoc_mem over widended mem:
		// results.add(createHavocMemCall(source, auxVarNames, true));
		// Add final assumption:
		results.add(createLoopInvariantAssumption(
				loop.getLoopInvariants(nodeFactory), auxVarNames));
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
	 * <code>
	 * 
	 * $mem loop_tmp_ws = write_set_peek();
	 * int loop_tmp_length = mem_to_pointers_size(ws);
	 * 
	 * if (loop_tmp_length > 0) {
	 *   void * _loop_tmp_ptrs[loop_tmp_length];
	 *   mem_to_pointers(loop_tmp_ws, _loop_tmp_ptrs); 
	 *   foreach (ptr : _loop_tmp_ptrs);
	 *     $assert(EXISTS ptr in m);
	 * }
	 * </code><br>
	 * 
	 * @throws SyntaxException
	 */
	private List<BlockItemNode> checkPointerBelongtoMemoryLocationSet(
			ExpressionNode writeSet, List<ExpressionNode> memoryLocarionSet,
			Source source, MemoryLocationManager memoryLocationManager)
			throws SyntaxException {
		List<BlockItemNode> results = new LinkedList<>();
		List<BlockItemNode> trueBranch = new LinkedList<>();
		String ws_size = nextLoopTmpIdentifier();
		String ws_ptrs = nextLoopTmpIdentifier();
		String ws_ele_idx = nextLoopTmpIdentifier();
		TypeNode intType = nodeFactory.newBasicTypeNode(source,
				BasicTypeKind.INT);
		TypeNode pointerArrayType;

		results.add(nodeFactory.newVariableDeclarationNode(source,
				identifier(ws_size), intType,
				functionCall(source, MEM_SIZE, Arrays.asList(writeSet))));
		pointerArrayType = nodeFactory.newArrayTypeNode(source,
				nodeFactory.newPointerTypeNode(source,
						nodeFactory.newVoidTypeNode(source)),
				identifierExpression(ws_size));

		trueBranch.add(nodeFactory.newVariableDeclarationNode(source,
				identifier(ws_ptrs), pointerArrayType));
		trueBranch
				.add(nodeFactory.newExpressionStatementNode(functionCall(source,
						MEM_TO_POINTER_ARRAY, Arrays.asList(writeSet.copy(),
								nodeFactory.newOperatorNode(source,
										Operator.ADDRESSOF, identifierExpression(
												ws_ptrs))))));
		// asserted existence:
		ExpressionNode ptrInAssignedLocations = memoryLocationManager
				.pointerBelongsToMemoryLocationSet(
						nodeFactory.newOperatorNode(source, Operator.SUBSCRIPT,
								identifierExpression(ws_ptrs),
								identifierExpression(ws_ele_idx)),
						memoryLocarionSet, source);
		VariableDeclarationNode ws_ele_idxDecl = nodeFactory
				.newVariableDeclarationNode(source, identifier(ws_ele_idx),
						intType.copy(),
						nodeFactory.newIntegerConstantNode(source, "0"));
		ForLoopInitializerNode loopInitializer = nodeFactory
				.newForLoopInitializerNode(source,
						Arrays.asList(ws_ele_idxDecl));
		ExpressionNode loopCondition = nodeFactory.newOperatorNode(source,
				Operator.LT, identifierExpression(ws_ele_idx),
				identifierExpression(ws_size));
		ExpressionNode loopIncrementer = nodeFactory.newOperatorNode(source,
				Operator.ASSIGN, identifierExpression(ws_ele_idx),
				nodeFactory.newOperatorNode(source, Operator.PLUS,
						identifierExpression(ws_ele_idx),
						nodeFactory.newIntegerConstantNode(source, "1")));

		trueBranch.add(nodeFactory.newForLoopNode(source, loopInitializer,
				loopCondition, loopIncrementer,
				nodeFactory.newExpressionStatementNode(
						functionCall(source, BaseWorker.ASSERT,
								Arrays.asList(ptrInAssignedLocations))),
				null));
		// create if-branch:
		results.add(nodeFactory.newIfNode(source,
				nodeFactory.newOperatorNode(source, Operator.LT,
						nodeFactory.newIntegerConstantNode(source, "0"),
						identifierExpression(ws_size)),
				nodeFactory.newCompoundStatementNode(source, trueBranch)));
		return results;
	}

	/**
	 * Creates an assertion function call with an argument "predicate".
	 * 
	 * @param predicate
	 *            The {@link ExpressionNode} which represents a predicate. It is
	 *            the only argument of an assertion call.
	 * @return A created assert call statement node;
	 * @throws SyntaxException
	 */
	private StatementNode createAssertion(ExpressionNode predicate)
			throws SyntaxException {
		ExpressionNode assertIdentifier = identifierExpression(
				BaseWorker.ASSERT);
		StringLiteralNode messageNode = nodeFactory
				.newStringLiteralNode(predicate.getSource(), violationMessage,
						astFactory.getTokenFactory()
								.newStringToken(
										loopInvariantsViolationMessageToken)
								.getStringLiteral());

		FunctionCallNode assumeCall = nodeFactory.newFunctionCallNode(
				predicate.getSource(), assertIdentifier,
				Arrays.asList(predicate.copy(), messageNode), null);
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
	private StatementNode createLoopInvariantAssumption(
			ExpressionNode predicate, AuxiliaryVariableNames auxVarNames) {
		ExpressionNode assumeIdentifier = identifierExpression(
				BaseWorker.ASSUME);
		ExpressionNode assumption = nodeFactory.newOperatorNode(
				predicate.getSource(), Operator.LAND, predicate.copy(),
				identifierExpression(auxVarNames.loop_mem_assumption));
		FunctionCallNode assumeCall = nodeFactory.newFunctionCallNode(
				predicate.getSource(), assumeIdentifier,
				Arrays.asList(assumption), null);

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
	private StatementNode createAssumptionPush(ExpressionNode predicate,
			AuxiliaryVariableNames auxVarNames) {
		ExpressionNode assumeIdentifier = identifierExpression(ASSUME_PUSH);
		ExpressionNode assumption = nodeFactory.newOperatorNode(
				predicate.getSource(), Operator.LAND, predicate.copy(),
				identifierExpression(auxVarNames.loop_mem_assumption));
		FunctionCallNode assumeCall = nodeFactory.newFunctionCallNode(
				predicate.getSource(), assumeIdentifier,
				Arrays.asList(assumption), null);

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
	 * 
	 * <p>
	 * Return statements : <code>
	 *   tmp_var = clause;
	 *   lhs &= tmp_var;
	 * </code> which is equivalent to <code>lhs &= clause</code>
	 * </p>
	 * <p>
	 * The reason of using a tmp_var is to prevent the short-circuit transformer
	 * to transform it to the following form : <code>
	 *    tmp_var = lhs
	 *    if (tmp_var) 
	 *      tmp_var = clause;
	 *      lhs = tmp_var;
	 * </code> which is functional equivalent to the ones above but we don't
	 * want the value of lhs to be moved to the path condition since it will be
	 * popped later.
	 * </p>
	 */
	private StatementNode createLogicalAndEquals(ExpressionNode lhs,
			ExpressionNode clause, Source source) {
		String tmp_var = nextLoopTmpIdentifier();
		BlockItemNode tmpDecl = nodeFactory.newVariableDeclarationNode(source,
				identifier(tmp_var),
				nodeFactory.newBasicTypeNode(source, BasicTypeKind.BOOL));
		StatementNode assignClause2Tmp = nodeFactory.newExpressionStatementNode(
				nodeFactory.newOperatorNode(source, Operator.ASSIGN,
						identifierExpression(tmp_var), clause));
		StatementNode lhsLandEqualsTmp = nodeFactory.newExpressionStatementNode(
				nodeFactory.newOperatorNode(source, Operator.ASSIGN, lhs,
						nodeFactory.newOperatorNode(source, Operator.LAND,
								lhs.copy(), identifierExpression(tmp_var))));

		return nodeFactory.newCompoundStatementNode(source,
				Arrays.asList(tmpDecl, assignClause2Tmp, lhsLandEqualsTmp));
	}

	/**
	 * 
	 * @return a <code>$write_set_push()</code> statement node;
	 */
	private StatementNode createWriteSetPush(Source source) {
		// TODO memObject currently not used...
		ExpressionNode wsPushIdentifier = identifierExpression(WRITE_SET_PUSH);
		FunctionCallNode wsPushCall = nodeFactory.newFunctionCallNode(source,
				wsPushIdentifier, Arrays.asList(), null);
		return nodeFactory.newExpressionStatementNode(wsPushCall);
	}

	/**
	 * 
	 * @return <code>$get_state()</code> call expression
	 */
	private ExpressionNode createGetStateCall(Source source,
			boolean fullState) {
		return nodeFactory.newFunctionCallNode(source,
				identifierExpression(fullState
						? REGULAR_GET_FULL_STATE_CALL
						: REGULAR_GET_STATE_CALL),
				Arrays.asList(), null);
	}

	/**
	 * 
	 * @return <code>$new_mem()</code> call expression
	 */
	private ExpressionNode createNewLoopWriteSetCall(Source source) {
		return nodeFactory.newFunctionCallNode(source,
				this.identifierExpression(LOOP_WRITE_SET_NEW), Arrays.asList(),
				null);
	}

	/**
	 * 
	 * @return <code>$state</code> type node
	 */
	private TypeNode createStateTypeNode(Source source) {
		return nodeFactory.newTypedefNameNode(identifier(STATE_TYPE), null);
	}

	/**
	 * Creates a write_set_pop() function call.
	 * 
	 * @return A created write set pop statement node;
	 */
	private ExpressionNode createWriteSetPop(Source source,
			AuxiliaryVariableNames auxVarNames) {
		ExpressionNode wsPopIdentifier = identifierExpression(WRITE_SET_POP);

		FunctionCallNode wsPopCall = nodeFactory.newFunctionCallNode(source,
				wsPopIdentifier, Arrays.asList(), null);
		return wsPopCall;
	}

	/**
	 * Creates an $loop_write_set_havoc($loop_write_set ws) function call:
	 * 
	 * @param var
	 *            An {@link ExpressionNode} representing an variable.
	 * @param AuxiliaryVariableNames
	 *            a group of auxiliary variable names
	 * @param referToPreState
	 *            the $havoc_mem operation always refer to a state
	 *            <code>s</code>, such that all the memory locations that are
	 *            not havoced, shall have values equal to what they are
	 *            evaluated in <code>s</code>. If referToPreState is false, the
	 *            <code>s</code> is by default $state_null (which means the
	 *            current state), otherwise, the <code>s</code> refers to the
	 *            loop pre-state.
	 * @return The created $havoc call expression node.
	 */
	private BlockItemNode createHavocMemCall(Source source,
			AuxiliaryVariableNames auxVarNames) {
		IdentifierNode memVarIdentifier = identifier(
				auxVarNames.loop_write_set);
		ExpressionNode callIdentifier = identifierExpression(
				LOOP_WRITE_SET_HAVOC);
		ExpressionNode varExpression = nodeFactory
				.newIdentifierExpressionNode(source, memVarIdentifier);
		ExpressionNode stateExpression = identifierExpression(
				auxVarNames.loop_pre_state);
		FunctionCallNode call = nodeFactory.newFunctionCallNode(source,
				callIdentifier, Arrays.asList(varExpression, stateExpression),
				null);
		ExpressionNode assign2lhs = nodeFactory.newOperatorNode(source,
				Operator.ASSIGN,
				identifierExpression(auxVarNames.loop_mem_assumption), call);

		return nodeFactory.newExpressionStatementNode(assign2lhs);
	}

	/**
	 * @return <code>$choose_int(2)</code> call.
	 * @throws SyntaxException
	 */
	private ExpressionNode createNDBinaryChoice(Source source)
			throws SyntaxException {
		return nodeFactory.newFunctionCallNode(source,
				identifierExpression(CHOOSE_INT),
				Arrays.asList(nodeFactory.newIntegerConstantNode(source, "2")),
				null);
	}

	/**
	 * @return <code>memcpy(dest, src, byteWiseSize)</code> call.
	 * @throws SyntaxException
	 */
	private BlockItemNode createMemcpyCall(Source source, ExpressionNode dest,
			ExpressionNode src, ExpressionNode byteWiseSize)
			throws SyntaxException {
		return nodeFactory.newExpressionStatementNode(
				nodeFactory.newFunctionCallNode(source,
						nodeFactory.newIdentifierExpressionNode(source,
								nodeFactory.newIdentifierNode(source,
										BaseWorker.MEMCPY)),
						Arrays.asList(dest, src, byteWiseSize), null));
	}

	/**
	 * Suppose the <code>ws</code> is the $loop_write_set auxiliary variable
	 * associated to the loop, this method returns <code>
	 * loop_mem = $loop_write_set_update(loop_mem, $write_set_pop());
	 * </code>
	 * 
	 * @throws SyntaxException
	 */
	private List<BlockItemNode> writeSetPopAndUpdate(Source source,
			LoopContractBlock loop, AuxiliaryVariableNames auxVarNames)
			throws SyntaxException {
		ExpressionNode ws = identifierExpression(auxVarNames.loop_write_set);
		ExpressionNode pop = createWriteSetPop(source, auxVarNames);
		ExpressionNode union = nodeFactory.newFunctionCallNode(source,
				identifierExpression(LOOP_WRITE_SET_UNION),
				Arrays.asList(ws, pop), null);
		ExpressionNode assign = nodeFactory.newOperatorNode(source,
				Operator.ASSIGN, ws.copy(), union);

		return Arrays.asList(nodeFactory.newExpressionStatementNode(assign));
	}

	/**
	 * <code>
	 * if (least_iters < n)
	 *   least_iters++;
	 * else {
	 *   loop_mem = $loop_write_set_widening(loop_mem);
	 *   loop_new_cond = $choose_int(2);
	 * }
	 * </code>
	 * 
	 * @throws SyntaxException
	 */
	private List<BlockItemNode> loopNewCondition(Source source,
			AuxiliaryVariableNames auxVarNames) throws SyntaxException {
		ExpressionNode leastItersVar = identifierExpression(
				auxVarNames.loop_least_iters_counter);
		ExpressionNode termCondVar = identifierExpression(
				auxVarNames.loop_new_cond);
		ExpressionNode leastItersPLUSone = nodeFactory.newOperatorNode(source,
				Operator.PLUS, leastItersVar,
				nodeFactory.newIntegerConstantNode(source, "1"));
		ExpressionNode leastIterCond = nodeFactory.newOperatorNode(source,
				Operator.LT, leastItersVar.copy(), LEAST_NUM_ITERATIONS.copy());
		ExpressionNode wideningCall;
		StatementNode trueBranch, falseBranch;
		List<BlockItemNode> wideningThenNDChoice = new LinkedList<>();

		wideningCall = nodeFactory.newFunctionCallNode(source,
				identifierExpression(LOOP_WRITE_SET_WIDENING),
				Arrays.asList(identifierExpression(auxVarNames.loop_write_set)),
				null);
		wideningThenNDChoice
				.add(nodeFactory.newExpressionStatementNode(
						nodeFactory.newOperatorNode(source, Operator.ASSIGN,
								identifierExpression(
										auxVarNames.loop_write_set),
								wideningCall)));
		wideningThenNDChoice.add(nodeFactory.newExpressionStatementNode(
				nodeFactory.newOperatorNode(source, Operator.ASSIGN,
						termCondVar, createNDBinaryChoice(source))));
		trueBranch = nodeFactory.newExpressionStatementNode(
				nodeFactory.newOperatorNode(source, Operator.ASSIGN,
						leastItersVar.copy(), leastItersPLUSone));
		falseBranch = nodeFactory.newCompoundStatementNode(source,
				wideningThenNDChoice);
		return Arrays.asList(nodeFactory.newIfNode(source, leastIterCond,
				trueBranch, falseBranch));
	}

	/**
	 * Wrap a {@link BlockItemNode} with an $assuming block
	 */
	@SuppressWarnings("unused")
	private List<BlockItemNode> wrapAssuming(ExpressionNode assumption,
			BlockItemNode body, AuxiliaryVariableNames auxVarNames) {
		List<BlockItemNode> results = new LinkedList<>();
		results.add(createAssumptionPush(assumption, auxVarNames));
		results.add(body);
		results.add(createAssumptionPop(body.getSource()));
		return results;
	}

	private static class AuxiliaryVariableNames {
		final String loop_write_set;
		final String loop_mem_assumption;
		final String loop_pre_state;
		final String loop_new_cond;
		final String loop_least_iters_counter;

		AuxiliaryVariableNames(String loop_write_set,
				String loop_mem_assumption, String loop_mem_pre_state,
				String loop_term_cond, String loop_least_iters_counters) {
			this.loop_write_set = loop_write_set;
			this.loop_mem_assumption = loop_mem_assumption;
			this.loop_pre_state = loop_mem_pre_state;
			this.loop_new_cond = loop_term_cond;
			this.loop_least_iters_counter = loop_least_iters_counters;
		}
	}
}
