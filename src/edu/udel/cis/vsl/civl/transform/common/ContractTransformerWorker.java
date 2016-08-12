package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssignsOrReadsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssumesNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.BehaviorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode.ContractKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.EnsuresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ExtendedQuantifiedExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ExtendedQuantifiedExpressionNode.ExtendedQuantifier;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPICollectiveBlockNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPICollectiveBlockNode.MPICollectiveKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractExpressionNode.MPIContractExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.RequiresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.WaitsforNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.LambdaNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.RegularRangeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ResultNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.ArrayTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.PointerTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode.TypeNodeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.front.IF.CivlcTokenConstant;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.common.ExprTriple;
import edu.udel.cis.vsl.abc.transform.common.SETriple;
import edu.udel.cis.vsl.abc.util.IF.Pair;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.transform.IF.ContractTransformer;

/**
 * This transformer serves for CIVL Contracts mode.
 * 
 * @author ziqingluo
 *
 */
public class ContractTransformerWorker extends BaseWorker {
	/**
	 * The common prefix for all generated identifiers, 'ctat' is short for
	 * 'contract':
	 */
	private final static String CONTRACT_VAR_PREFIX = "_ctat_";

	/**
	 * $havoc system function identifier:
	 */
	private final static String HAVOC = "$havoc";

	/**
	 * MPI_Comm typedef name:
	 */
	private final static String MPI_COMM_TYPE = "MPI_Comm";

	/**
	 * The default MPI communicator identifier:
	 */
	private final static String MPI_COMM_WORLD = "MPI_COMM_WORLD";

	/**
	 * A constant which is defined by the CIVL-C extention of ACSL:
	 */
	private final static String MPI_COMM_SIZE_CONST = "$mpi_comm_size";

	/**
	 * A constant which is defined by the CIVL-C extention of ACSL:
	 */
	private final static String MPI_COMM_RANK_CONST = "$mpi_comm_rank";

	/**
	 * An MPI routine identifier:
	 */
	private final static String MPI_COMM_SIZE_CALL = "MPI_Comm_size";

	/**
	 * An MPI routine identifier:
	 */
	private final static String MPI_COMM_RANK_CALL = "MPI_Comm_rank";

	/**
	 * An MPI routine identifier:
	 */
	private final static String MPI_INIT_CALL = "MPI_Init";

	/**
	 * An MPI routine identifier:
	 */
	private final static String MPI_FINALIZE_CALL = "MPI_Finalize";

	/**
	 * A CIVL-MPI function identifier:
	 */
	private final static String MPI_SNAPSHOT = "$mpi_snapshot";

	/**
	 * A CIVL-MPI function identifier:
	 */
	private final static String MPI_UNSNAPSHOT = "$mpi_unsnapshot";

	/**
	 * A CIVL-MPI function identifier:
	 */
	private final static String MPI_EXTENTOF = "$mpi_extentof";

	/**
	 * A CIVL-MPI function identifier:
	 */
	private final static String MPI_SIZEOF = "sizeofDatatype";

	/**
	 * A CIVL-MPI function identifier:
	 */
	private final static String MPI_CONTRACT_ENTERS = "$mpi_contract_enters";

	/**
	 * A CIVL-MPI function identifier:
	 */
	private final static String MPI_CONTRACT_ENTERED = "$mpi_contract_entered";

	/**
	 * A CIVL-MPI function identifier:
	 */
	private final static String MPI_ASSIGNS = "$mpi_assigns";

	/**
	 * A comm-library function identifier:
	 */
	private final static String COMM_EMPTY_IN = "$comm_empty_in";

	/**
	 * A comm-library function identifier:
	 */
	private final static String COMM_EMPTY_OUT = "$comm_empty_out";

	/**
	 * p2p field of an MPI_Comm sturct object:
	 */
	private final static String P2P = "p2p";

	/**
	 * col field of an MPI_Comm sturct object:
	 */
	private final static String COL = "col";

	/**
	 * A collate-library function identifier:
	 */
	private final static String COLLATE_COMPLETE = "$collate_complete";

	/**
	 * A collate-library function identifier:
	 */
	private final static String COLLATE_ARRIVED = "$collate_arrived";

	/**
	 * A collate-library function identifier:
	 */
	private final static String COLLATE_STATE = "$collate_state";

	/**
	 * Collate library system function identifier:
	 */
	private final static String COLLATE_GET_STATE = "$collate_get_state";

	/**
	 * Civl-c library system function identifier:
	 */
	private final static String GET_STATE = "$get_state";

	/**
	 * Within each function (either non-target : )
	 */
	/**
	 * A pre-call collate state identifier:
	 */
	private final static String COLLATE_STATE_VAR_PRE = "pre_cp";

	/**
	 * A post-call collate state identifier:
	 */
	private final static String COLLATE_STATE_VAR_POST = "post_cp";

	/**
	 * The name prefix for a driver function
	 */
	private final static String DRIVER_PREFIX = "_driver_";

	/**
	 * An identifier representing the returned value of a contracted function
	 * call:
	 */
	private final static String RESULT = "$result";

	/**
	 * A string source for a return statement:
	 */
	private final static String RETURN_RESULT = "return $result;";

	/**
	 * A string source for a return statement:
	 */
	private final static String COPY = "$copy";

	private final static String TMP_HEAP_PREFIX = CONTRACT_VAR_PREFIX
			+ "_heap_";

	private int tmpHeapCounter = 0;

	private final static String TMP_EXTENT_PREFIX = CONTRACT_VAR_PREFIX
			+ "_extent_";

	private int tmpExtentCounter = 0;

	private final static String TMP_OLD_PREFIX = CONTRACT_VAR_PREFIX + "_old_";

	private int tmpOldCounter = 0;

	private int tmpRemoteInLambdaCounter = 0;

	private Set<VariableDeclarationNode> globalVarDecls = new HashSet<>();

	/**
	 * This class represents a contract behavior. Without loss of generality,
	 * there is always a default behavior which has no assumption and name.
	 * 
	 * A contract behavior consists of a set of contract clauses which specify
	 * properties. Currently it consists of "requires", "ensures" and "waitsfor"
	 * clauses. The design of this class is make it extensible if new clauses
	 * will be supported later.
	 * 
	 * @author ziqing
	 *
	 */
	private class ConditionalClauses {
		/**
		 * The condition which comes from the assumption of a behavior:
		 */
		private ExpressionNode condition;

		private List<ExpressionNode> requiresSet;

		private List<ExpressionNode> ensuresSet;

		private List<ExpressionNode> waitsforSet;

		private List<ExpressionNode> assignsSet;

		ConditionalClauses(ExpressionNode condition) {
			this.condition = condition;
			requiresSet = new LinkedList<>();
			ensuresSet = new LinkedList<>();
			waitsforSet = new LinkedList<>();
			assignsSet = new LinkedList<>();
		}

		/**
		 * Add an expression of a "requires" clause.
		 * 
		 * @param requires
		 */
		private void addRequires(ExpressionNode requires) {
			requiresSet.add(requires);
		}

		/**
		 * Add an expression of a "ensures" clause.
		 * 
		 * @param requires
		 */
		private void addEnsures(ExpressionNode ensures) {
			ensuresSet.add(ensures);
		}

		/**
		 * Add a set of arguments of a "waitsfor" clause.
		 * 
		 * @param requires
		 */
		private void addWaitsfor(SequenceNode<ExpressionNode> waitsforArgs) {
			for (ExpressionNode arg : waitsforArgs)
				waitsforSet.add(arg);
		}

		/**
		 * Add a set of arguments of a "assigns" clause.
		 * 
		 * @param assignsArgs
		 */
		private void addAssigns(SequenceNode<ExpressionNode> assignsArgs) {
			for (ExpressionNode arg : assignsArgs)
				assignsSet.add(arg);
		}

		/**
		 * Returns all requires expressions in this contract behavior
		 * 
		 * @param nodeFactory
		 *            A reference to the {@link NodeFactory}
		 * @return
		 */
		private List<ExpressionNode> getRequires(NodeFactory nodeFactory) {
			if (requiresSet.isEmpty())
				return requiresSet;

			ExpressionNode result = requiresSet.remove(0);

			result.remove();
			for (ExpressionNode requires : requiresSet) {
				requires.remove();
				result = nodeFactory.newOperatorNode(requires.getSource(),
						Operator.LAND, result, requires);
			}
			requiresSet.clear();
			requiresSet.add(result);
			return requiresSet;
		}

		/**
		 * Returns all ensures expressions in this contract behavior
		 * 
		 * @param nodeFactory
		 *            A reference to the {@link NodeFactory}
		 * @return
		 */
		private List<ExpressionNode> getEnsures(NodeFactory nodeFactory) {
			if (ensuresSet.isEmpty())
				return ensuresSet;

			ExpressionNode result = ensuresSet.remove(0);

			result.remove();
			for (ExpressionNode ensures : ensuresSet) {
				ensures.remove();
				result = nodeFactory.newOperatorNode(ensures.getSource(),
						Operator.LAND, result, ensures);
			}
			ensuresSet.clear();
			ensuresSet.add(result);
			return ensuresSet;

		}

		/**
		 * Returns a list of arguments of "waitsfor" clauses
		 * 
		 * @param nodeFactory
		 * @return
		 */
		private List<ExpressionNode> getWaitsfors() {
			return waitsforSet;
		}

		/**
		 * Return a list of assigns arguments.
		 * 
		 * @return
		 */
		private List<ExpressionNode> getAssignsArgs() {
			return assignsSet;
		}
	}

	/**
	 * This class represents a contract block, i.e. either all of the contracts
	 * for sequential properties or one MPI collective contract block. A
	 * contract block contains a set of {@link ConditionalClauses} which
	 * represents the body of the contract block.
	 * 
	 * @author ziqing
	 *
	 */
	private class ParsedContractBlock {
		/**
		 * The expression represents an MPI communicator which associates to an
		 * MPI collective block.
		 */
		private ExpressionNode mpiComm;
		/**
		 * The expression represents the choice of which MPI communicator is
		 * used for the contracts in the contract block: point-2-point or
		 * collective.
		 */
		private MPICollectiveKind pattern;
		/**
		 * A list of {@link ConditionalClauses} which represents the body of the
		 * block.
		 */
		private List<ConditionalClauses> behaviors;

		/**
		 * The {@link Source} associates to the contract block
		 */
		private Source source;
		/**
		 * A flag indicates if the contract block is completed. A complete
		 * contract block should never contain any {@link ConditionalClauses}
		 * that saves empty clauses.
		 */
		private boolean complete = false;

		ParsedContractBlock(ExpressionNode mpiComm, MPICollectiveKind pattern,
				Source source) {
			behaviors = new LinkedList<>();
			this.mpiComm = mpiComm;
			this.pattern = pattern;
			this.source = source;
		}

		/**
		 * Clean up all {@link ConditionalClauses} in this contract block. If a
		 * {@link ConditionalClauses} has empty clauses, remove it.
		 * 
		 * @return True if and only if there is at least one
		 *         {@link ConditionalClauses} remaining at the end of the
		 *         function.
		 */
		private boolean complete() {
			List<ConditionalClauses> newBehaviors = new LinkedList<>();

			for (ConditionalClauses behav : behaviors) {
				if (!(behav.requiresSet.isEmpty() && behav.ensuresSet.isEmpty()
						&& behav.waitsforSet.isEmpty()))
					newBehaviors.add(behav);
			}
			complete = true;
			behaviors = newBehaviors;
			return !behaviors.isEmpty();
		}

		/**
		 * <p>
		 * <b>Pre-condition:</b> The contract block must be complete
		 * </p>
		 * 
		 * @return A list of {@link ConditionalClauses} which is the body of the
		 *         contract block.
		 */
		private List<ConditionalClauses> getConditionalClauses() {
			assert complete : "Cannot get ConditionalClauses before the contract block is complete";
			return behaviors;
		}

		/**
		 * <p>
		 * <b>Pre-condition:</b> The contract block must be complete
		 * </p>
		 * 
		 * @return A list of pairs. Each pair consists of a conditional
		 *         expression and a list of arguments of "waitsfor" clauses.
		 */
		private List<Pair<ExpressionNode, List<ExpressionNode>>> getConditionalWaitsfors() {
			assert complete : "Cannot get ConditionalClauses before the contract block is complete";
			List<Pair<ExpressionNode, List<ExpressionNode>>> results = new LinkedList<>();

			for (ConditionalClauses condClause : behaviors)
				results.add(new Pair<>(condClause.condition,
						condClause.waitsforSet));
			return results;
		}

		/**
		 * <p>
		 * <b>Pre-condition:</b> The contract block must NOT be complete
		 * </p>
		 * <p>
		 * <b>Summary:</b> Add a {@link ConditionalClauses} into the contract
		 * block.
		 * </p>
		 */
		private void addConditionalClauses(ConditionalClauses clauses) {
			assert !complete : "Cannot add ConditionalClauses after the contract block is complete";
			behaviors.add(clauses);
		}
	}

	/* ********************* Private class fields: ********************** */
	/**
	 * The target function that will be verified independently. Other functions
	 * will be not verified. For other functions that been annotated with
	 * contracts, the transformer will remove their bodies, since only their
	 * contracts are used.
	 */
	private final String targetFunctionName;

	/**
	 * {@link Source} of <code>int $mpi_comm_size, $mpi_comm_rank;</code>
	 */
	private Source mpiCommSizeSource, mpiCommRankSource;

	public ContractTransformerWorker(ASTFactory astFactory,
			String targetFunctionName) {
		super(ContractTransformer.LONG_NAME, astFactory);
		identifierPrefix = CONTRACT_VAR_PREFIX;
		this.targetFunctionName = targetFunctionName;
		mpiCommSizeSource = newSource("int " + MPI_COMM_SIZE_CONST + ";",
				CivlcTokenConstant.DECLARATION);
		mpiCommRankSource = newSource("int " + MPI_COMM_RANK_CONST + ";",
				CivlcTokenConstant.DECLARATION);
	}

	/* ************************* Public methods: ************************** */
	@Override
	public AST transform(AST ast) throws SyntaxException {
		SequenceNode<BlockItemNode> root = ast.getRootNode();
		String sourceFileName;
		List<BlockItemNode> externalList = new LinkedList<>();
		Pair<FunctionDefinitionNode, List<BlockItemNode>> processedSourceFiles;
		SequenceNode<BlockItemNode> newRootNode;
		List<BlockItemNode> sourceFiles = new LinkedList<>();
		List<BlockItemNode> globalVarHavocs;
		boolean hasMPI = false;
		AST newAst;
		int count;

		ast.release();
		transformMainFunction(root);
		/*
		 * Step 1: process source file: For all functions f in source file, if f
		 * is the target function, transform f with "transformTargetFunction";
		 * Else if f is contracted, transform f with
		 * "transformAnnotatedFunction"; Else, keep f unchanged (f might be
		 * executed with it's definition or may never be used).
		 */
		for (BlockItemNode child : root) {
			// Some nodes that been removed or added by previous
			// transformers
			// will not and cannot be processed here:
			if (child == null || child.getSource() == null)
				continue;
			sourceFileName = child.getSource().getFirstToken().getSourceFile()
					.getName();
			// TODO: currently we assume that source file are only C
			// programs,
			// libraries are all ends with ".cvh" or ".cvl":
			if (sourceFileName.endsWith(".c")) {
				child.remove();
				sourceFiles.add(child);
			}
			if (!hasMPI && sourceFileName.equals("mpi.h"))
				hasMPI = true;
		}
		globalVarHavocs = havocForGlobalVariables(sourceFiles);
		// process function definitions and declarations in source files:
		processedSourceFiles = processSourceFileNodes(sourceFiles, hasMPI);
		// create declarations for all functions that will be used later:
		count = root.numChildren();
		for (int i = 0; i < count; i++) {
			BlockItemNode child = root.getSequenceChild(i);

			if (child != null) {
				root.removeChild(i);
				externalList.add(child);
			}
		}
		// externalList.addAll(createDeclarationsForUsedFunctions());
		externalList.addAll(processedSourceFiles.right);
		// $havoc for all global variables:
		externalList.addAll(globalVarHavocs);
		externalList.add(mainFunction(processedSourceFiles.left, hasMPI));
		newRootNode = nodeFactory.newSequenceNode(
				newSource("TranslationUnit",
						CivlcTokenConstant.TRANSLATION_UNIT),
				"TranslationUnit", externalList);
		completeSources(newRootNode);
		newAst = astFactory.newAST(newRootNode, ast.getSourceFiles(),
				ast.isWholeProgram());
		newAst.prettyPrint(System.out, false);
		return newAst;
	}

	/* ******************* Primary transforming methods: ******************** */
	/**
	 * <p>
	 * <b>Summary: </b> Create a new main function which creates variables for
	 * each formal parameters of the driver function, then calls the driver
	 * function. If the MPI library is included, wrap the call to driver with a
	 * pair of <code>MPI_Init and MPI_Finalize</code>.
	 * 
	 * @param targetFunc
	 *            The target function. The driver of the target function will be
	 *            called in the created main function.
	 * @param hasMPI
	 *            If MPI library is included.
	 * @return The created main function definition node
	 * @throws SyntaxException
	 */
	private FunctionDefinitionNode mainFunction(
			FunctionDefinitionNode targetFunc, boolean hasMPI)
			throws SyntaxException {
		List<BlockItemNode> items = new LinkedList<BlockItemNode>();
		StatementNode callDriver;

		callDriver = nodeFactory
				.newExpressionStatementNode(nodeFactory.newFunctionCallNode(
						newSource(targetFunc.getName() + "(...);",
								CivlcTokenConstant.CALL),
						identifierExpression(
								DRIVER_PREFIX + targetFunc.getName()),
						Arrays.asList(), null));
		if (hasMPI) {
			// insert MPI_Init and MPI_Destroy
			items.add(createMPIInitCall());
			items.add(callDriver);
			items.add(createMPIFinalizeCall());
		} else
			items.add(callDriver);

		CompoundStatementNode mainBody = nodeFactory.newCompoundStatementNode(
				newSource("main body", CivlcTokenConstant.COMPOUND_STATEMENT),
				items);
		SequenceNode<VariableDeclarationNode> mainFormals = nodeFactory
				.newSequenceNode(
						this.newSource(
								"formal parameter of the declaration of the main function",
								CivlcTokenConstant.DECLARATION_LIST),
						"FormalParameterDeclarations",
						new ArrayList<VariableDeclarationNode>());
		FunctionTypeNode mainType = nodeFactory.newFunctionTypeNode(
				this.newSource("type of the main function",
						CivlcTokenConstant.TYPE),
				this.basicType(BasicTypeKind.INT), mainFormals, true);

		return nodeFactory.newFunctionDefinitionNode(
				this.newSource("definition of the main function",
						CivlcTokenConstant.FUNCTION_DEFINITION),
				this.identifier("main"), mainType, null, mainBody);
	}

	/**
	 * <p>
	 * <b>Summary</b> Searches functions in source files. For functions with
	 * contracts but are not the target function, replacing a definition for
	 * them; for the target function, create a driver function for it.
	 * 
	 * @param sourceFileNodes
	 * @return A pair of a {@link FunctionDefinitionNode} which represents thet
	 *         target function and a list of processed source file contents.
	 * @throws SyntaxException
	 */
	private Pair<FunctionDefinitionNode, List<BlockItemNode>> processSourceFileNodes(
			List<BlockItemNode> sourceFileNodes, boolean hasMpi)
			throws SyntaxException {
		List<BlockItemNode> newSourceFileNodes = new LinkedList<>();
		FunctionDefinitionNode target = null;

		for (BlockItemNode child : sourceFileNodes) {
			if (child.nodeKind() == NodeKind.FUNCTION_DECLARATION
					|| child.nodeKind() == NodeKind.FUNCTION_DEFINITION) {
				FunctionDeclarationNode funcDecl = (FunctionDeclarationNode) child;

				// If the function declaration has definition, test if it is
				// the
				// target function:
				if (funcDecl.isDefinition()) {
					FunctionDefinitionNode funcDefi = (FunctionDefinitionNode) funcDecl;
					if (funcDefi.getName().equals(targetFunctionName)) {
						// Keep the original function definition of the
						// target
						// function:
						newSourceFileNodes.add(funcDefi);
						newSourceFileNodes
								.add(transformTargetFunction(funcDefi, hasMpi));
						// It is not allowed that there are two function
						// definitions with the same name, so the processing
						// can
						// keep going and this branch shall never be enterd
						// again.
						target = funcDefi;
						target.getContract().remove();
						continue;
					}
				} else
					newSourceFileNodes.add(funcDecl);
				// If the function declaration is contracted, create a
				// harness
				// definition for it, it's original definition will not be
				// added
				// into the new source file components if it is defined in
				// source files:
				if (isSourceFileFunctionContracted(funcDecl)) {
					FunctionDefinitionNode defiOfThis;

					newSourceFileNodes
							.add(transformContractedFunction(funcDecl, hasMpi));
					if ((defiOfThis = funcDecl.getEntity()
							.getDefinition()) != null)
						defiOfThis.remove();
				}
			} else {
				newSourceFileNodes.add(child);
				continue;
			}
		}
		if (target == null)
			throw new CIVLSyntaxException("Target function: "
					+ this.targetFunctionName + " not existing!");
		return new Pair<>(target, newSourceFileNodes);
	}

	/**
	 * <p>
	 * <b>Summary: </b> Transform a non-target contracted function into a
	 * deductive executable form.
	 * </p>
	 * 
	 * <p>
	 * <b>Details: </b> The body of a non-target contracted function f will be
	 * added or replaced with: <code>
	 * f () {
	 *   assert ( seq-requires );
	 *   cp = snapshot();
	 *   $run $when($collate_complete(cp) $with(cp) 
	 *      if (assumes-cond)
	 *         assert ( col-requires );
	 *         
	 *   int $result;
	 *   
	 *   $havoc(&$result);
	 *   assume( seq-ensures);
	 *   if (assume-cond)
	 *      $wit(cp) assume(non-sync-col-ensures);
	 *   $run {  
	 *     if (assume-cond)
	 *        $when($collate_arrived(cp, args .. )) $with(cp)
	 *           assume(sync-col-ensures);
	 *   }
	 * }
	 * 
	 * </code>
	 * </p>
	 * 
	 * @param funcDecl
	 *            The {@link FunctionDeclarationNode} of the transformed
	 *            function. It's original body will be removed.
	 * @return
	 * @throws SyntaxException
	 */
	private FunctionDefinitionNode transformContractedFunction(
			FunctionDeclarationNode funcDecl, boolean hasMpi)
			throws SyntaxException {
		CompoundStatementNode body;
		FunctionTypeNode funcTypeNode = funcDecl.getTypeNode();
		List<BlockItemNode> bodyItems = new LinkedList<>();
		List<BlockItemNode> localAssumes4ensurances = new LinkedList<>();
		List<BlockItemNode> tmpVars4localOldExprs = new LinkedList<>();
		Source contractSource = funcDecl.getContract().getSource();
		Source mpiCommRankSource = newSource("int " + MPI_COMM_RANK_CONST + ";",
				CivlcTokenConstant.DECLARATION);
		Source mpiCommSizeSource = newSource("int " + MPI_COMM_SIZE_CONST + ";",
				CivlcTokenConstant.DECLARATION);
		TypeNode intTypeNode;
		List<ParsedContractBlock> parsedContractBlocks;
		ParsedContractBlock localBlock = null;
		boolean returnVoid = false;

		// Transform step 1: Inserts assertions for sequential requirements:
		parsedContractBlocks = parseFunctionContracts(funcDecl.getContract());
		localBlock = factorOutSequentialBlock(parsedContractBlocks);
		if (localBlock != null)
			for (ConditionalClauses condClause : localBlock
					.getConditionalClauses())
				for (ExpressionNode requires : condClause
						.getRequires(nodeFactory))
					bodyItems.addAll(translateConditionalPredicates(false,
							condClause.condition, requires.copy()).left);

		// Transform local ensurances to assumes, add temporary variable
		// declarations for old expressions:
		if (localBlock != null) {
			for (ConditionalClauses condClauses : localBlock
					.getConditionalClauses())
				for (ExpressionNode ensures : condClauses
						.getEnsures(nodeFactory)) {
					tmpVars4localOldExprs.addAll(
							replaceOldExpressionNodes4Local(ensures, hasMpi));
					localAssumes4ensurances
							.addAll(translateConditionalPredicates(true,
									condClauses.condition,
									ensures.copy()).left);
				}
		}
		// Transform step 2: Inserts $mpi_comm_rank and $mpi_comm_size:
		intTypeNode = nodeFactory.newBasicTypeNode(
				newSource("int", CivlcTokenConstant.TYPE), BasicTypeKind.INT);
		bodyItems.add(nodeFactory.newVariableDeclarationNode(mpiCommRankSource,
				identifier(MPI_COMM_RANK_CONST), intTypeNode));
		bodyItems.add(nodeFactory.newVariableDeclarationNode(mpiCommSizeSource,
				identifier(MPI_COMM_SIZE_CONST), intTypeNode.copy()));
		// Add temporary variable declarations for old expressions:
		bodyItems.addAll(tmpVars4localOldExprs);
		// Transform step 3: Takes a snapshot and inserts assertions for
		// requirements of each MPI-collective block:
		for (ParsedContractBlock mpiBlock : parsedContractBlocks)
			bodyItems.addAll(transformCoRequirements4NT(mpiBlock));

		returnVoid = isVoidType(
				funcDecl.getTypeNode().getReturnType().getType());
		// Transform step 4: Inserts $result declaration:
		if (!returnVoid) {
			bodyItems.add(nodeFactory.newVariableDeclarationNode(contractSource,
					identifier(RESULT),
					funcDecl.getTypeNode().getReturnType().copy()));
			bodyItems.add(nodeFactory.newExpressionStatementNode(
					createHavocCall(identifierExpression(RESULT))));
		}
		// Transform step 5: Translate assigns clauses:
		for (ParsedContractBlock mpiBlock : parsedContractBlocks)
			for (ConditionalClauses condClause : mpiBlock.behaviors)
				bodyItems.addAll(processConditionalAssignsArgumentNode(
						condClause.condition, condClause.getAssignsArgs()));

		// Transform step 6: Insert assumes for sequential ensurances:
		bodyItems.addAll(localAssumes4ensurances);

		// Transform step 7: Insert assumes for ensurances of each
		// MPI-collective block:
		for (ParsedContractBlock block : parsedContractBlocks)
			bodyItems.addAll(transformCoEnsurances4NT(block));
		// Unsnapshots for pre-:
		for (ParsedContractBlock mpiBlock : parsedContractBlocks)
			bodyItems.add(nodeFactory.newExpressionStatementNode(
					createMPIUnsnapshotCall(mpiBlock.mpiComm)));
		// Unsnapshots for post-:
		for (ParsedContractBlock mpiBlock : parsedContractBlocks)
			bodyItems.add(nodeFactory.newExpressionStatementNode(
					createMPIUnsnapshotCall(mpiBlock.mpiComm)));
		if (!returnVoid)
			bodyItems.add(nodeFactory.newReturnNode(
					newSource(RETURN_RESULT, CivlcTokenConstant.RETURN),
					identifierExpression(RESULT)));
		body = nodeFactory.newCompoundStatementNode(funcDecl.getSource(),
				bodyItems);
		return nodeFactory.newFunctionDefinitionNode(funcDecl.getSource(),
				funcDecl.getIdentifier().copy(), funcTypeNode.copy(), null,
				body);
	}

	/**
	 * <p>
	 * <b>Summary:</b> Wraps the target function with a harness function. The
	 * harness is created based on the contracts of the target function.
	 * </p>
	 * <p>
	 * <b>Details:</b> The contracted function will be transformed into the
	 * following pattern:
	 * <ul>
	 * <b> driver( ... ) { </b>
	 * <li>1 localContractStatements;</li>
	 * <li>2 $mpi_comm_size and $mpi_comm_rank decl;</li>
	 * <li>3 MPI_Comm_size(comm, &$mpi_comm_size) && MPI_Comm_rank( ... );</li>
	 * <li>4 take-snapshot;</li>
	 * <li>5 collectiveContractStatements</li>
	 * <li>6 enters</li>
	 * <li>7 $result declaration && call target function</li>
	 * <li>8 entered check</li>
	 * <li>9 localContractStatements;</li>
	 * <li>10 take-snapshot;</li>
	 * <li>11 collectiveContractStatements</li> <b>}</b>
	 * </p>
	 * 
	 * @param funcDefi
	 *            The definition of the target function
	 * @return A new driver function for the target function.
	 * @throws SyntaxException
	 */
	private FunctionDefinitionNode transformTargetFunction(
			FunctionDefinitionNode funcDefi, boolean hasMpi)
			throws SyntaxException {
		CompoundStatementNode body;
		ExpressionNode funcIdentifier = identifierExpression(
				funcDefi.getName());
		FunctionTypeNode funcTypeNode = funcDefi.getTypeNode();
		List<ExpressionNode> funcParamIdentfiers = new LinkedList<>();
		List<BlockItemNode> bodyItems = new LinkedList<>();
		List<BlockItemNode> tmpVarDecls4OldExprs = new LinkedList<>();
		List<BlockItemNode> assert4localEnsures = new LinkedList<>();
		String driverName = DRIVER_PREFIX + funcDefi.getName();
		Source contractSource = funcDefi.getContract().getSource();
		Source driverSource = newSource(driverName,
				CivlcTokenConstant.FUNCTION_DEFINITION);
		TypeNode intTypeNode;

		// Re-organize contract nodes:
		List<ParsedContractBlock> parsedContractBlocks = parseFunctionContracts(
				funcDefi.getContract());
		ParsedContractBlock localBlock = factorOutSequentialBlock(
				parsedContractBlocks);

		// Create variable declarations which are actual parameters of the
		// target function:
		bodyItems.addAll(createVariableDeclsAndInitsForDriver(funcTypeNode));

		// Transform step 1: Insert assumes for sequential requires:
		if (localBlock != null)
			for (ConditionalClauses requires : localBlock
					.getConditionalClauses())
				for (ExpressionNode pred : requires.getRequires(nodeFactory)) {
					Pair<List<OperatorNode>, ExpressionNode> valids_newPred = getValidExpressionNodes(
							pred.copy());

					bodyItems.addAll(translateConditionalPredicates(true,
							requires.condition, valids_newPred.right).left);

					for (OperatorNode valid : valids_newPred.left)
						bodyItems.addAll(createMallocStatementSequenceFoValid(
								valid, funcDefi));
				}
		// Transform sequential ensurances into asserts, add temporary variable
		// declarations here for old expressions:
		if (localBlock != null)
			for (ConditionalClauses ensures : localBlock
					.getConditionalClauses())
				for (ExpressionNode pred : ensures.getEnsures(nodeFactory)) {
					tmpVarDecls4OldExprs.addAll(
							replaceOldExpressionNodes4Local(pred, hasMpi));
					assert4localEnsures
							.addAll(translateConditionalPredicates(false,
									ensures.condition, pred.copy()).left);
				}
		// Transform step 2: Add $mpi_comm_rank and $mpi_comm_size variables:
		intTypeNode = nodeFactory.newBasicTypeNode(
				newSource("int", CivlcTokenConstant.TYPE), BasicTypeKind.INT);
		bodyItems.add(nodeFactory.newVariableDeclarationNode(mpiCommRankSource,
				identifier(MPI_COMM_RANK_CONST), intTypeNode));
		bodyItems.add(nodeFactory.newVariableDeclarationNode(mpiCommSizeSource,
				identifier(MPI_COMM_SIZE_CONST), intTypeNode.copy()));
		// Add temporary variable declarations here for old expressions:
		bodyItems.addAll(tmpVarDecls4OldExprs);
		// Transform step 3-5: Takes a snapshot and insert assumes for requires
		// in each MPI-collective block:
		for (ParsedContractBlock mpiBlock : parsedContractBlocks)
			bodyItems.addAll(transformCoRequirements4Target(mpiBlock,
					mpiCommRankSource, mpiCommSizeSource));

		// Transform step 6: Inserts $mpi_contract_enters(MPI_Comm ):
		// for (ParsedContractBlock mpiBlock : parsedContractBlocks)
		// bodyItems.add(createMPIContractEnters(mpiBlock.mpiComm));

		// Transform step 7: T $result = f( ... );:
		ExpressionNode targetCall;

		for (VariableDeclarationNode param : funcTypeNode.getParameters())
			funcParamIdentfiers
					.add(identifierExpression(param.getIdentifier().name()));
		targetCall = nodeFactory.newFunctionCallNode(driverSource,
				funcIdentifier.copy(), funcParamIdentfiers, null);
		if (!isVoidType(funcDefi.getTypeNode().getReturnType().getType()))
			bodyItems.add(nodeFactory.newVariableDeclarationNode(contractSource,
					identifier(RESULT),
					funcDefi.getTypeNode().getReturnType().copy(), targetCall));
		else
			bodyItems.add(nodeFactory.newExpressionStatementNode(targetCall));
		// Transform step 8: Inserts "$mpi_contract_entered"s:
		// for (ParsedContractBlock mpiBlock : parsedContractBlocks)
		// for (Pair<ExpressionNode, List<ExpressionNode>> condWaitsforArgs :
		// mpiBlock
		// .getConditionalWaitsfors())
		// bodyItems.add(checkWaitsfors(condWaitsforArgs.left,
		// condWaitsforArgs.right, mpiBlock.mpiComm,
		// mpiBlock.source));

		// Transform step 9: Insert sequential assertions:
		bodyItems.addAll(assert4localEnsures);

		// Transform step 10-11: Inserts snapshot and collective assertions for
		// ensures of each MPI-collective block:
		for (ParsedContractBlock mpiBlock : parsedContractBlocks)
			bodyItems.addAll(transformCollectiveEnsures4Target(mpiBlock));
		// Unsnapshots for pre-:
		for (ParsedContractBlock mpiBlock : parsedContractBlocks)
			bodyItems.add(nodeFactory.newExpressionStatementNode(
					createMPIUnsnapshotCall(mpiBlock.mpiComm)));
		// Unsnapshots for post-:
		for (ParsedContractBlock mpiBlock : parsedContractBlocks)
			bodyItems.add(nodeFactory.newExpressionStatementNode(
					createMPIUnsnapshotCall(mpiBlock.mpiComm)));
		// Free for $mpi_valid() calls at requirements:
		// for (ParsedContractBlock mpiBlock : parsedContractBlocks)
		// for (ConditionalClauses condClauses : mpiBlock
		// .getConditionalClauses())
		// for (ExpressionNode requires : condClauses
		// .getRequires(nodeFactory)) {
		// List<MPIContractExpressionNode> mpiValids =
		// getMPIValidExpressionNodes(
		// requires);
		// bodyItems.addAll(
		// createConditionalFreeCalls(null, mpiValids));
		// }
		body = nodeFactory.newCompoundStatementNode(driverSource, bodyItems);
		funcTypeNode = nodeFactory.newFunctionTypeNode(funcTypeNode.getSource(),
				funcTypeNode.getReturnType().copy(),
				nodeFactory.newSequenceNode(
						funcTypeNode.getParameters().getSource(),
						"contract_driver_parameters", Arrays.asList()),
				funcTypeNode.hasIdentifierList());
		return nodeFactory.newFunctionDefinitionNode(driverSource,
				identifier(driverName), funcTypeNode.copy(), null, body);
	}

	/* ***************** Helpers for transforming methods: ****************** */
	/**
	 * Returns true if and only if the given function has been annotated with
	 * requirements , ensurances or MPI collective blocks and the function is
	 * defined in source files.
	 * 
	 * @param funcDecl
	 *            The {@link FunctionDeclarationNode} of a function that will be
	 *            judged if it is contracted.
	 * @return True if and only if the given function has been annotated with
	 *         requirements , ensurances or MPI collective blocks and it is
	 *         defined in source files. Otherwise, false.
	 */
	private boolean isSourceFileFunctionContracted(
			FunctionDeclarationNode funcDecl) {
		if (!funcDecl.isDefinition())
			if (!funcDecl.getEntity().getDefinition().getSource()
					.getFirstToken().getSourceFile().getName().endsWith(".c"))
				return false;
		if (funcDecl.getContract() == null)
			return false;
		for (ContractNode contract : funcDecl.getContract()) {
			ContractKind kind = contract.contractKind();

			switch (kind) {
				case REQUIRES :
				case ENSURES :
				case MPI_COLLECTIVE :
					return true;
				default :
					continue;
			}
		}
		return false;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Transforms all requirements in a given
	 * {@link MPICollectiveBlockNode} to assumptions.
	 * </p>
	 * 
	 * <p>
	 * <b>Details: </b>In the driver function, requirements in each MPI
	 * collective block will be transformed to: <code>
	 * {
	 *   MPI_Comm_rank(comm, &$mpi_comm_rank);
	 *   MPI_Comm_size(comm, &$mpi_comm_size);
	 *   $when($collate_complte(cp) $with(cp) {
	 *      if(behavior-assumption)
	 *        assume( all-requires);
	 *   }
	 * }
	 * </code>
	 * </p>
	 * 
	 * @param contract
	 *            The {@link MPICollectiveBlockNode} representing a MPI
	 *            collective block.
	 * @param mpiCommRankSource
	 *            The {@link Source} of the $mpi_comm_rank
	 * @param mpiCommSizeSource
	 *            The {@link Source} of the $mpi_comm_size
	 * @return A list of {@link BlockItemNode} representing all the transformed
	 *         statements
	 * @throws SyntaxException
	 */
	private List<BlockItemNode> transformCoRequirements4Target(
			ParsedContractBlock mpiBlock, Source mpiCommRankSource,
			Source mpiCommSizeSource) throws SyntaxException {
		ExpressionNode mpiComm = mpiBlock.mpiComm;
		VariableDeclarationNode collateStateDecl = createCollateStateDeclaration(
				COLLATE_STATE_VAR_PRE, mpiComm);
		StatementNode coAssumeStmt;
		List<BlockItemNode> coAssumesComponents = new LinkedList<>();
		List<BlockItemNode> bodyItems = new LinkedList<>();

		bodyItems.addAll(mpiConstantsInitialization(mpiComm));
		// Add $mpi_valid() calls for \mpi_valid annotations:
		for (ConditionalClauses condClauses : mpiBlock.getConditionalClauses())
			for (ExpressionNode requires : condClauses
					.getRequires(nodeFactory)) {
				List<MPIContractExpressionNode> mpiValids = getMPIValidExpressionNodes(
						requires);

				for (MPIContractExpressionNode mpiValid : mpiValids) {
					bodyItems.addAll(createMallocStatementSequenceForMPIValid2(
							mpiValid));
				}
			}
		for (ConditionalClauses condClauses : mpiBlock.getConditionalClauses())
			for (ExpressionNode requires : condClauses
					.getRequires(nodeFactory)) {
				Pair<List<BlockItemNode>, List<BlockItemNode>> assumesAndTmpVar = translateConditionalPredicates(
						true, condClauses.condition, requires);

				bodyItems.addAll(assumesAndTmpVar.right);
				coAssumesComponents.addAll(assumesAndTmpVar.left);
			}
		// take snapshot after do $mpi_valid which elaborates "datatype"s:
		bodyItems.add(collateStateDecl);
		if (coAssumesComponents.isEmpty())
			return bodyItems;
		// $when ($complete) $with(...) { $assume( ... ) } :
		coAssumeStmt = nodeFactory.newCompoundStatementNode(mpiBlock.source,
				coAssumesComponents);
		coAssumeStmt = nodeFactory.newWithNode(coAssumeStmt.getSource(),
				identifierExpression(collateStateDecl.getName()), coAssumeStmt);
		bodyItems.add(execAfterComplete(
				identifierExpression(collateStateDecl.getName()), coAssumeStmt,
				coAssumeStmt.getSource()));
		return bodyItems;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Transforms all requirements in a given
	 * {@link MPICollectiveBlockNode} to assertions. Similar to
	 * {@link #transformCollectiveRequires4Target(MPICollectiveBlockNode, Source, Source)}
	 * except for replacing "$assume" with "assert".
	 * </p>
	 *
	 * <p>
	 * <b>Details: </b>Requirements in each MPI collective block will be
	 * transformed to: <code>
	 * {
	 *   MPI_Comm_rank(comm, &$mpi_comm_rank);
	 *   MPI_Comm_size(comm, &$mpi_comm_size);
	 *   $run {
	 *     $when($collate_complte(cp) $with(cp) {
	 *        if(behavior-assumption)
	 *          assert(all-requires);
	 *        ...
	 *       assert( $comm_empty_in(comm)
	 *               && $comm_empty_out(comm));
	 *     }
	 *   }
	 * }
	 * </code>
	 * </p>
	 * 
	 * @param mpiBlock
	 *            The {@link ParsedContractBlock} representing a MPI collective
	 *            block.
	 * @param mpiCommRankSource
	 *            The {@link Source} of the $mpi_comm_rank
	 * @param mpiCommSizeSource
	 *            The {@link Source} of the $mpi_comm_size
	 * @return A list of {@link BlockItemNode} representing all the transformed
	 *         statements
	 * @throws SyntaxException
	 */
	private List<BlockItemNode> transformCoRequirements4NT(
			ParsedContractBlock mpiBlock) throws SyntaxException {
		ExpressionNode mpiComm = mpiBlock.mpiComm;
		VariableDeclarationNode collateStateDecl = createCollateStateDeclaration(
				COLLATE_STATE_VAR_PRE, mpiComm);
		List<BlockItemNode> coAssertsComponents = new LinkedList<>();
		List<BlockItemNode> bodyItems = new LinkedList<>();
		StatementNode stmt;

		bodyItems.addAll(mpiConstantsInitialization(mpiComm));
		for (ConditionalClauses condClauses : mpiBlock.getConditionalClauses())
			for (ExpressionNode requires : condClauses
					.getRequires(nodeFactory)) {
				Pair<List<BlockItemNode>, List<BlockItemNode>> assertsAndTmpVars = translateConditionalPredicates(
						false, condClauses.condition, requires.copy());

				bodyItems.addAll(assertsAndTmpVars.right);
				coAssertsComponents.addAll(assertsAndTmpVars.left);
			}
		bodyItems.add(collateStateDecl);
		// $comm_empty_in && $comm_empty_out:
		coAssertsComponents.add(
				createAssertion(commEmptyInAndOut(mpiComm, mpiBlock.pattern)));
		// $run $when($complete(..)) $with(...) { assert(..) }:
		stmt = nodeFactory.newCompoundStatementNode(mpiBlock.source,
				coAssertsComponents);
		stmt = nodeFactory.newWithNode(stmt.getSource(),
				identifierExpression(collateStateDecl.getName()), stmt);
		bodyItems.add(runAfterComplete(
				identifierExpression(collateStateDecl.getName()), stmt,
				stmt.getSource()));
		return bodyItems;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Transforms all ensurances in a given
	 * {@link MPICollectiveBlockNode} to assertions.
	 * </p>
	 * 
	 * <p>
	 * <b>Details: </b> In the driver function, ensurances in each MPI
	 * collective block will be transformed to: <code>
	 * $when ($collate_complete(cp)) $with(cp) { 
	 *     if (behavior-assumption)
	 *       assert(ensurances);
	 * }
	 * </code>
	 * </p>
	 * 
	 * @param mpiCommAndClauses
	 * @return
	 * @throws SyntaxException
	 */
	private List<BlockItemNode> transformCollectiveEnsures4Target(
			ParsedContractBlock mpiBlock) throws SyntaxException {
		ExpressionNode mpiComm = mpiBlock.mpiComm;
		VariableDeclarationNode collateStateDecl = createCollateStateDeclaration(
				COLLATE_STATE_VAR_POST, mpiComm);
		StatementNode stmt;
		List<BlockItemNode> bodyItems = new LinkedList<>();
		List<BlockItemNode> asserts = new LinkedList<>();

		// $when($complete(...)) $with(...) { assert }:
		for (ConditionalClauses condClauses : mpiBlock
				.getConditionalClauses()) {
			StatementNode withStmt;
			List<BlockItemNode> coAssertStmtComponents = new LinkedList<>();

			for (ExpressionNode ensures : condClauses.getEnsures(nodeFactory)) {
				Pair<List<BlockItemNode>, List<BlockItemNode>> assertsAndTmpVar;

				ensures = replaceOldExpressionNodes4collective(ensures.copy());
				assertsAndTmpVar = translateConditionalPredicates(false,
						condClauses.condition, ensures);
				bodyItems.addAll(assertsAndTmpVar.right);
				coAssertStmtComponents.addAll(assertsAndTmpVar.left);
			}
			if (!coAssertStmtComponents.isEmpty()) {
				stmt = nodeFactory.newCompoundStatementNode(mpiBlock.source,
						coAssertStmtComponents);
				withStmt = nodeFactory.newWithNode(stmt.getSource(),
						identifierExpression(collateStateDecl.getName()), stmt);
				asserts.add(execAfterComplete(
						identifierExpression(collateStateDecl.getName()),
						withStmt, withStmt.getSource()));
			}
		}
		// $collate_state cp = $collate_snapshot():
		bodyItems.add(collateStateDecl);
		bodyItems.addAll(asserts);
		stmt = createAssertion(commEmptyInAndOut(mpiComm, mpiBlock.pattern));
		bodyItems.add(execAfterComplete(
				identifierExpression(collateStateDecl.getName()), stmt,
				stmt.getSource()));
		return bodyItems;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Transforms all ensurances in a given
	 * {@link MPICollectiveBlockNode} to assumes.
	 * </p>
	 * 
	 * <p>
	 * <b>Details: </b> This method gets a "if-guarded_then" statement by
	 * calling
	 * {@link #translateBehavedPred(boolean, ExpressionNode, ConditionalClausePredicates)}
	 * for each {@link ConditionalClausePredicates} in behavedClausesList. If
	 * the "if-guarded_then" statement really contains a guard (i.e. the
	 * corresponding {@link ConditionalClausePredicates#waitsforRanges != null}
	 * ), then the statement should be run by $run (kind like a deamon process).
	 * </p>
	 * 
	 * @param mpiComm
	 *            An expression node representing an MPI communicator
	 * @param behavedClausesList
	 *            A list of {@link behavedClausesList} which represents all
	 *            ensurances under named-behavior assumptions with waitsfor
	 *            clauses in one MPI collective block.
	 * @return
	 */
	private List<BlockItemNode> transformCoEnsurances4NT(
			ParsedContractBlock mpiBlock) {
		List<BlockItemNode> bodyItems = new LinkedList<>();
		List<BlockItemNode> asserts = new LinkedList<>();
		List<BlockItemNode> tmpVars = new LinkedList<>();
		VariableDeclarationNode collateStateDecl = createCollateStateDeclaration(
				COLLATE_STATE_VAR_POST, mpiBlock.mpiComm);

		for (ConditionalClauses condClauses : mpiBlock.getConditionalClauses())
			for (ExpressionNode ensures : condClauses.getEnsures(nodeFactory)) {
				Pair<StatementNode, List<BlockItemNode>> assertsAndTempVar = translateEnsurance2Inference(
						identifierExpression(collateStateDecl.getName()),
						condClauses.condition, ensures.copy(),
						condClauses.getWaitsfors());
				asserts.add(assertsAndTempVar.left);
				tmpVars.addAll(assertsAndTempVar.right);
			}
		bodyItems.addAll(tmpVars);
		bodyItems.add(collateStateDecl);
		bodyItems.addAll(asserts);
		return bodyItems;
	}

	/*
	 * ************************* Helper methods ****************************
	 */
	/**
	 * <p>
	 * <b>Summary:</b> Translate a {@link ConditionalClausePredicates} to a
	 * if-then (assume/assert) statement. Specially, if the "condition" field in
	 * the {@link ConditionalClausePredicates} is null, the if condition can be
	 * omitted.
	 * </p>
	 * 
	 * @param isAssume
	 *            Flag indicates if the if-then statement wraps a $assume or an
	 *            "assert".
	 * @param behavedExprs
	 *            A {@link ConditionalClausePredicates} which gives branch
	 *            conditions and expressions as predicates for either assume or
	 *            assert.
	 * @return LEFT: The translated if-then statement; RIGHT tmpVarsDecls which
	 *         should be added at outside of the with block.
	 * @throws SyntaxException
	 */
	private Pair<List<BlockItemNode>, List<BlockItemNode>> translateConditionalPredicates(
			boolean isAssume, ExpressionNode cond, ExpressionNode preds)
			throws SyntaxException {
		List<BlockItemNode> stmts = new LinkedList<>();
		ExpressionNode conditionNeedsChecking = null;// =
														// condition4ErrorChecking(preds);
		Pair<List<BlockItemNode>, ExpressionNode> replaceDatatype;

		replaceDatatype = transformMPIDatatype2extentofDatatype(preds);
		preds = replaceDatatype.right;
		stmts.add(isAssume ? createAssumption(preds) : createAssertion(preds));
		if (conditionNeedsChecking != null)
			stmts.add(createAssertion(conditionNeedsChecking));

		// If the condition is null, it doesn't need a
		// branch:
		if (cond != null) {
			StatementNode stmt = nodeFactory
					.newCompoundStatementNode(preds.getSource(), stmts);

			stmt = nodeFactory.newIfNode(cond.getSource(), cond.copy(), stmt);
			return new Pair<>(Arrays.asList(stmt), replaceDatatype.left);
		}
		return new Pair<>(stmts, replaceDatatype.left);
	}

	/**
	 * <p>
	 * <b>Precondition: collateStateRef.parent() == null</b>
	 * </p>
	 * <p>
	 * <b>Summary: </b>Translate a {@link ConditionalClausePredicates} to a
	 * if-guarded_then (assume/assert) statement. if-guarded_then generally has
	 * such a form: <code>
	 *  if( cond ) {
	 *     $when(guard) {
	 *       statement... ;
	 *     }
	 *  }
	 * </code> Specially, if the "condition" field in the
	 * {@link ConditionalClausePredicates} is null, the if condition can be
	 * omitted. If the "waitsfor" field in the
	 * {@link ConditionalClausePredicates} is null, the when guard can be
	 * omitted.
	 * </p>
	 * 
	 * @param collateStateRef
	 *            The expression which represents the $collate_state object
	 * @param condition
	 *            The condition upon the given ensurances.
	 * @param ensurance
	 *            The ensurance expression
	 * @param waitsforArgs
	 *            A set of arguments of "waitsfor" clauses
	 * @param source
	 *            The {@link Source} associates with the ensurances.
	 * @return
	 */
	private Pair<StatementNode, List<BlockItemNode>> translateEnsurance2Inference(
			ExpressionNode collateStateRef, ExpressionNode condition,
			ExpressionNode ensurance, List<ExpressionNode> waitsforArgs) {
		assert collateStateRef.parent() == null;
		boolean hasGuard = !waitsforArgs.isEmpty();
		StatementNode stmt;
		Pair<List<BlockItemNode>, ExpressionNode> tmpVarDecls_pred;

		tmpVarDecls_pred = transformMPIDatatype2extentofDatatype(ensurance);
		ensurance = tmpVarDecls_pred.right;
		ensurance = replaceOldExpressionNodes4collective(ensurance);
		stmt = createAssumption(ensurance);
		stmt = nodeFactory.newWithNode(collateStateRef.getSource(),
				collateStateRef.copy(), stmt);
		if (hasGuard) {
			ExpressionNode guard = createCollateArrivedCall(waitsforArgs,
					collateStateRef);

			stmt = nodeFactory.newWhenNode(guard.getSource(), guard, stmt);
		}
		// If the condition is null, it doesn't need a
		// branch:
		if (condition != null)
			stmt = nodeFactory.newIfNode(condition.getSource(),
					condition.copy(), stmt);
		// if (hasGuard)
		// stmt = nodeFactory.newRunNode(stmt.getSource(), stmt);
		return new Pair<>(stmt, tmpVarDecls_pred.left);
	}

	/**
	 * <p>
	 * <b>Summary: </b> Creates <code>$mpi_contract_entered( args )</code> call
	 * for an MPI communicator. The call is to check if all "waited" MPI
	 * processes already entered the target function.
	 * </p>
	 * 
	 * @param assumption
	 *            Behavior assumptions, if <code>assumption != null </code>,
	 *            then an if-then branch is introduced.
	 * @param waitsforArgs
	 *            A sequence of "waitsfor" arguments.
	 * @param mpiComm
	 *            An expression node which represents an MPI communicator.
	 * @return Generated call statement (may be with "if" conditions).
	 */
	private StatementNode checkWaitsfors(ExpressionNode assumption,
			List<ExpressionNode> waitsforArgs, ExpressionNode mpiComm,
			Source source) {
		ExpressionNode pred = createMPIContractEntered(waitsforArgs, mpiComm);
		StatementNode stmt = createAssertion(pred);

		if (assumption != null)
			stmt = nodeFactory.newIfNode(assumption.getSource(),
					assumption.copy(), stmt);
		return stmt;
	}

	/*
	 * ************************* Utility methods ****************************
	 */
	/**
	 * Replace all appearances of {@link ResultNode} with an identifier
	 * expression "$result" for the given expression;
	 * 
	 * @param expression
	 * @return
	 */
	private ExpressionNode replaceResultNode2Identifier(
			ExpressionNode expression) {
		ExpressionNode newExpr = expression.copy();
		ASTNode child = newExpr;

		while (child != null) {
			if (child instanceof ResultNode) {
				ASTNode parent = child.parent();
				int childIndex = child.childIndex();

				child.remove();
				child = identifierExpression(RESULT);
				parent.setChild(childIndex, child);
			}
			child = child.nextDFS();
		}
		return newExpr;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Creates an assertion function call with an argument
	 * "predicate".
	 * </p>
	 * 
	 * @param predicate
	 *            The {@link ExpressionNode} which represents a predicate. It is
	 *            the only argument of an assertion call.
	 * @param source
	 *            The {@link Source} of the created function call statement
	 *            node;
	 * @return A created assert call statement node;
	 */
	private StatementNode createAssertion(ExpressionNode predicate) {
		ExpressionNode noResultNodePredicate = replaceResultNode2Identifier(
				predicate);
		ExpressionNode assertIdentifier = identifierExpression(ASSERT);
		FunctionCallNode assertCall = nodeFactory.newFunctionCallNode(
				predicate.getSource(), assertIdentifier,
				Arrays.asList(noResultNodePredicate), null);
		return nodeFactory.newExpressionStatementNode(assertCall);
	}

	/**
	 * <p>
	 * <b>Summary: </b> Creates an assumption function call with an argument
	 * "predicate".
	 * </p>
	 * 
	 * @param predicate
	 *            The {@link ExpressionNode} which represents a predicate. It is
	 *            the only argument of an assumption call.
	 * @param source
	 *            The {@link Source} of the created function call statement
	 *            node;
	 * @return A created assumption call statement node;
	 */
	private StatementNode createAssumption(ExpressionNode predicate) {
		ExpressionNode noResultNodePredicate = replaceResultNode2Identifier(
				predicate);
		ExpressionNode assumeIdentifier = identifierExpression(ASSUME);
		FunctionCallNode assumeCall = nodeFactory.newFunctionCallNode(
				predicate.getSource(), assumeIdentifier,
				Arrays.asList(noResultNodePredicate), null);
		return nodeFactory.newExpressionStatementNode(assumeCall);
	}

	/**
	 * <p>
	 * <b>Summary: </b> Creates an MPI_Comm_rank function call:<code>
	 * MPI_Comm_rank(mpiComm, &variableRank);</code>
	 * </p>
	 * 
	 * @param mpiComm
	 *            An {@link ExpressionNode} representing an MPI communicator.
	 * 
	 * @param rankVar
	 *            An {@link ExpressionNode} representing an variable.
	 * @param source
	 *            The {@link Source} of the created call statement;
	 * @return The created MPI_Comm_rank call statement node.
	 */
	private StatementNode createMPICommRankCall(ExpressionNode mpiComm,
			ExpressionNode rankVar) {
		ExpressionNode callIdentifier = identifierExpression(
				MPI_COMM_RANK_CALL);
		ExpressionNode addressOfRank = nodeFactory.newOperatorNode(
				rankVar.getSource(), Operator.ADDRESSOF, rankVar.copy());
		FunctionCallNode call = nodeFactory.newFunctionCallNode(
				mpiCommRankSource, callIdentifier,
				Arrays.asList(mpiComm.copy(), addressOfRank), null);
		return nodeFactory.newExpressionStatementNode(call);
	}

	/**
	 * <p>
	 * <b>Summary: </b> Creates an MPI_Comm_size function call:<code>
	 * MPI_Comm_size(mpiComm, &variableRank);</code>
	 * </p>
	 * 
	 * @param mpiComm
	 *            An {@link ExpressionNode} representing an MPI communicator.
	 * 
	 * @param variableRank
	 *            An {@link ExpressionNode} representing an variable.
	 * @param source
	 *            The {@link Source} of the created call statement;
	 * @return The created MPI_Comm_size call statement node.
	 */
	private StatementNode createMPICommSizeCall(ExpressionNode mpiComm,
			ExpressionNode sizeVar) {
		ExpressionNode callIdentifier = identifierExpression(
				MPI_COMM_SIZE_CALL);
		ExpressionNode addressOfSize = nodeFactory.newOperatorNode(
				sizeVar.getSource(), Operator.ADDRESSOF, sizeVar.copy());
		FunctionCallNode call = nodeFactory.newFunctionCallNode(
				mpiCommSizeSource, callIdentifier,
				Arrays.asList(mpiComm.copy(), addressOfSize), null);
		return nodeFactory.newExpressionStatementNode(call);
	}

	/**
	 * <p>
	 * <b>Summary: </b> Creates an $mpi_snapshot function call:<code>
	 * $mpi_snapshot(mpiComm, $scope);</code>
	 * </p>
	 * 
	 * @param mpiComm
	 *            An {@link ExpressionNode} representing an MPI communicator.
	 * @return The created $mpi_snapshot call statement node.
	 */
	private ExpressionNode createMPISnapshotCall(ExpressionNode mpiComm) {
		Source source = newSource(MPI_SNAPSHOT, CivlcTokenConstant.CALL);
		Source hereSource = newSource("$here", CivlcTokenConstant.HERE);
		ExpressionNode callIdentifier = identifierExpression(MPI_SNAPSHOT);
		ExpressionNode hereNode = nodeFactory.newHereNode(hereSource);
		FunctionCallNode call = nodeFactory.newFunctionCallNode(source,
				callIdentifier, Arrays.asList(mpiComm.copy(), hereNode), null);

		return call;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Creates an $mpi_unsnapshot function call:<code>
	 * $mpi_unsnapshot(mpiComm);</code>
	 * </p>
	 * 
	 * @param mpiComm
	 *            An {@link ExpressionNode} representing an MPI communicator.
	 * @return The created $mpi_unsnapshot call statement node.
	 */
	private ExpressionNode createMPIUnsnapshotCall(ExpressionNode mpiComm) {
		Source source = newSource(MPI_UNSNAPSHOT, CivlcTokenConstant.CALL);
		ExpressionNode callIdentifier = identifierExpression(MPI_UNSNAPSHOT);
		FunctionCallNode call = nodeFactory.newFunctionCallNode(source,
				callIdentifier, Arrays.asList(mpiComm.copy()), null);

		return call;
	}

	/**
	 * Creates an <code>$mpi_contract_enters(mpiComm)</code> call.
	 * 
	 * @param mpiComm
	 *            An expression node represents an MPI communicator.
	 * @param source
	 *            The {@link Source} of the call.
	 * @return
	 */
	private StatementNode createMPIContractEnters(ExpressionNode mpiComm) {
		Source source = newSource(MPI_CONTRACT_ENTERS, CivlcTokenConstant.CALL);
		ExpressionNode callIdentifier = identifierExpression(
				MPI_CONTRACT_ENTERS);
		FunctionCallNode call = nodeFactory.newFunctionCallNode(source,
				callIdentifier, Arrays.asList(mpiComm.copy()), null);
		return nodeFactory.newExpressionStatementNode(call);
	}

	/**
	 * Creates an <code>$mpi_contract_entered(mpiComm, args ... )</code> call.
	 * 
	 * @param mpiComm
	 *            An expression node represents an MPI communicator.
	 * @param source
	 *            The {@link Source} of the call.
	 * @return
	 */
	private ExpressionNode createMPIContractEntered(List<ExpressionNode> ranges,
			ExpressionNode mpiComm) {
		Source source = newSource(
				MPI_CONTRACT_ENTERED + "(" + mpiComm + ", ...)",
				CivlcTokenConstant.CALL);
		ExpressionNode callIdentifier = identifierExpression(
				MPI_CONTRACT_ENTERED);
		List<ExpressionNode> arguments = new LinkedList<>();

		arguments.add(mpiComm.copy());
		for (ExpressionNode range : ranges)
			arguments.add(range.copy());

		FunctionCallNode call = nodeFactory.newFunctionCallNode(source,
				callIdentifier, arguments, null);
		return call;
	}

	/**
	 * Creates an <code>MPI_Init(NULL, NULL);</code> call statememt node.
	 * 
	 * @return The created statement node
	 * @throws SyntaxException
	 */
	private StatementNode createMPIInitCall() throws SyntaxException {
		IntegerConstantNode zero = nodeFactory.newIntegerConstantNode(
				newSource("0", CivlcTokenConstant.INTEGER_CONSTANT), "0");
		TypeNode ptr2Void = nodeFactory.newPointerTypeNode(
				newSource("(void *)", CivlcTokenConstant.TYPE),
				nodeFactory.newVoidTypeNode(
						newSource("void", CivlcTokenConstant.TYPE)));
		CastNode nullPtr = nodeFactory.newCastNode(
				newSource("(void *)0", CivlcTokenConstant.CAST), ptr2Void,
				zero);
		return nodeFactory
				.newExpressionStatementNode(nodeFactory.newFunctionCallNode(
						newSource("MPI_Init(NULL, NULL);",
								CivlcTokenConstant.CALL),
						identifierExpression(MPI_INIT_CALL),
						Arrays.asList(nullPtr, nullPtr.copy()), null));
	}

	/**
	 * Creates an <code>createMPIFinalizeCall();</code> call statement node.
	 * 
	 * @return The created statement node
	 */
	private StatementNode createMPIFinalizeCall() {
		return nodeFactory
				.newExpressionStatementNode(nodeFactory.newFunctionCallNode(
						newSource("MPI_Finalize();", CivlcTokenConstant.CALL),
						identifierExpression(MPI_FINALIZE_CALL),
						Arrays.asList(), null));
	}

	/**
	 * *
	 * <p>
	 * <b>Summary: </b> Creates an variable declaration:<code>
	 * $collate_state _conc_varName# = $mpi_snapshot(mpiComm);</code>
	 * </p>
	 * 
	 * @param varName
	 *            The String type variable name, it will be concatenated with
	 *            transformer prefix and counter.
	 * @param mpiComm
	 *            An expression represents an MPI communicator
	 * @param source
	 *            The {@link Source} attached with this declaration.
	 * @return The created declaration node.
	 */
	private VariableDeclarationNode createCollateStateDeclaration(
			String varName, ExpressionNode mpiComm) {
		Source source = newSource(COLLATE_STATE + " " + COLLATE_STATE_VAR_PRE
				+ " = " + MPI_SNAPSHOT, CivlcTokenConstant.DECLARATION);
		InitializerNode initializer = createMPISnapshotCall(mpiComm.copy());
		TypeNode collateStateTypeName = nodeFactory
				.newTypedefNameNode(identifier(COLLATE_STATE), null);
		String generatedVarName = identifierPrefix + varName;
		IdentifierNode varIdent = identifier(generatedVarName);

		return nodeFactory.newVariableDeclarationNode(source, varIdent,
				collateStateTypeName, initializer);
	}

	/**
	 * <p>
	 * <b>Summary: </b> Creates an $havoc function call:<code>
	 * $mpi_snapshot(&var);</code>
	 * </p>
	 * 
	 * @param var
	 *            An {@link ExpressionNode} representing an variable.
	 * @return The created $havoc call expression node.
	 */
	private ExpressionNode createHavocCall(ExpressionNode var) {
		Source source = newSource(
				HAVOC + "(" + var.prettyRepresentation() + ");",
				CivlcTokenConstant.CALL);
		ExpressionNode callIdentifier = identifierExpression(HAVOC);
		ExpressionNode addressOfVar = nodeFactory.newOperatorNode(
				var.getSource(), Operator.ADDRESSOF, var.copy());
		FunctionCallNode call = nodeFactory.newFunctionCallNode(source,
				callIdentifier, Arrays.asList(addressOfVar), null);

		return call;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Creates an $collate_complete function call:<code>
	 * $collate_complete(cp); </code> where cp is an expression represents a
	 * reference to a program state.
	 * </p>
	 * 
	 * @param stateRef
	 *            The expression represents a reference to a program state. It
	 *            is the only argument of a $collate_complete function
	 * @param source
	 *            The {@link Source} attached with the returned
	 *            {@link ExpressionNode}
	 * @return An {@link ExpressionNode} represents a $collate_complete function
	 *         call
	 */
	private ExpressionNode createCollateCompleteCall(ExpressionNode stateRef,
			Source source) {
		ExpressionNode completeFuncId = identifierExpression(COLLATE_COMPLETE);
		return nodeFactory.newFunctionCallNode(source, completeFuncId,
				Arrays.asList(stateRef.copy()), null);
	}

	/**
	 * <p>
	 * <b>Pre-condition: </b> <code>
	 *    withStatement.parent() == null; </code>
	 * </p>
	 * <p>
	 * <b>Summary: </b> Given two nodes "stateRef" which represents a reference
	 * to a collate state and "withStatement" which represents a statement that
	 * will be attached with a $with keyword, creates <br>
	 * <code>
	 * $run {
	 *   $atomic {
	 *   	$when ($collate_complete(collate-state-ref)) $with withStatement;
	 *   }
	 * }
	 * </code>
	 * </p>
	 * 
	 * @param collateStateRef
	 *            An expression node which represents a reference to a collate
	 *            state.
	 * @param withStatement
	 *            A statement node which represents a statement that will be
	 *            attached with a $with keyword
	 * @param source
	 *            The {@link Source} associates to the created statement.
	 * @return A block of statements as described in <b>Summary</b>
	 */
	private StatementNode runAfterComplete(ExpressionNode collateStateRef,
			StatementNode withStatement, Source source) {
		StatementNode stmt;

		stmt = execAfterComplete(collateStateRef, withStatement, source);
		return nodeFactory.newRunNode(source, stmt);
	}

	/**
	 * <p>
	 * <b>Pre-condition: </b> <code>
	 *    withStatement.parent() == null; </code>
	 * </p>
	 * <p>
	 * <b>Summary: </b> Given two nodes "stateRef" which represents a reference
	 * to a collate state and "withStatement" which represents a statement that
	 * will be attached with a $with keyword, creates <br>
	 * <code>
	 *   	$when ($collate_complete(collate-state-ref)) $with withStatement;
	 * </code>
	 * </p>
	 * 
	 * @param collateStateRef
	 *            An expression node which represents a reference to a collate
	 *            state.
	 * @param withStatement
	 *            A statement node which represents a statement that will be
	 *            attached with a $with keyword
	 * @param source
	 *            The {@link Source} associates to the created statement.
	 * @return A block of statements as described in <b>Summary</b>
	 */
	private StatementNode execAfterComplete(ExpressionNode collateStateRef,
			StatementNode withStatement, Source source) {
		assert withStatement.parent() == null;
		ExpressionNode completeOnStateRef = createCollateCompleteCall(
				collateStateRef, source);

		return nodeFactory.newWhenNode(completeOnStateRef.getSource(),
				completeOnStateRef.copy(), withStatement);

	}

	/**
	 * *
	 * <p>
	 * <b>Summary: </b> Creates an $collate_arrived function call:<code>
	 * $collate_arrived(cp, ... ); </code> where range is a $range type
	 * expression ;cp is an expression represents a reference to a program
	 * state.
	 * </p>
	 * 
	 * @param range
	 *            The expression with $range type. It is the first argument of
	 *            the $collate_arrived function call.
	 * @param stateRef
	 *            The expression represents a reference to a program state. It
	 *            is the second argument of a $collate_arrived function
	 * @return An {@link ExpressionNode} represents a $collate_arrived function
	 *         call
	 */
	private ExpressionNode createCollateArrivedCall(List<ExpressionNode> ranges,
			ExpressionNode stateRef) {
		Source source = newSource(COLLATE_ARRIVED + "(...)",
				CivlcTokenConstant.CALL);
		ExpressionNode arrivedFuncId = identifierExpression(COLLATE_ARRIVED);
		List<ExpressionNode> arguments = new LinkedList<>();

		arguments.add(stateRef.copy());
		for (ExpressionNode range : ranges)
			arguments.add(range.copy());
		return nodeFactory.newFunctionCallNode(source, arrivedFuncId, arguments,
				null);
	}

	/**
	 * Given an {@link MPICollectiveBlockNode}
	 * <code>\collective(MPI_Comm, P2P/COL): ...</code>, creates such a
	 * expression:
	 * <code>$mpi_empty_in(MPI_Comm.(p2p/col)) && $mpi_empty_out(MPI_Comm.(p2p/col))</code>
	 * 
	 * @param mpiCollectiveBlock
	 *            The given {@link MPICollectiveBlockNode}
	 * @return
	 */
	private ExpressionNode commEmptyInAndOut(ExpressionNode mpiComm,
			MPICollectiveKind colKind) {
		ExpressionNode arg, result;
		StringBuffer mpiCommPretty = mpiComm.prettyRepresentation();
		Source source = newSource("$comm_empty_in(" + mpiCommPretty
				+ ") && $comm_empty_out(" + mpiCommPretty + ");",
				CivlcTokenConstant.CALL);

		arg = colKind == MPICollectiveKind.P2P
				? nodeFactory.newDotNode(mpiComm.getSource(), mpiComm.copy(),
						identifier(P2P))
				: nodeFactory.newDotNode(mpiComm.getSource(), mpiComm.copy(),
						identifier(COL));
		result = nodeFactory.newFunctionCallNode(source,
				identifierExpression(COMM_EMPTY_IN), Arrays.asList(arg), null);
		return nodeFactory.newOperatorNode(source, Operator.LAND, result,
				nodeFactory.newFunctionCallNode(source,
						identifierExpression(COMM_EMPTY_OUT),
						Arrays.asList(arg.copy()), null));
	}

	/**
	 * Creates two statements: <code>
	 * MPI_Comm_rank(comm, &$mpi_comm_rank);
	 * MPI_Comm_size(comm, &$mpi_comm_size);
	 * </code>
	 * 
	 * @param mpiComm
	 *            The expression represents an MPI communicator
	 * @param mpiCommRankSource
	 *            The {@link Source} of the <code>$mpi_comm_rank</code>.
	 * @param mpiCommSizeSource
	 *            The {@link Source} of the <code>$mpi_comm_size</code>.
	 * @return
	 */
	private List<BlockItemNode> mpiConstantsInitialization(
			ExpressionNode mpiComm) {
		List<BlockItemNode> results = new LinkedList<>();

		results.add(createMPICommRankCall(mpiComm.copy(),
				identifierExpression(MPI_COMM_RANK_CONST)));
		results.add(createMPICommSizeCall(mpiComm.copy(),
				identifierExpression(MPI_COMM_SIZE_CONST)));
		return results;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Transform the parameters of the target function into a
	 * sequence of variable declarations. All of them will be initialized with
	 * arbitrary values.
	 * </p>
	 * 
	 * @param targetFuncType
	 *            A {@link FunctionTypeNode} which represents the function type
	 *            of the target function.
	 * @return
	 */
	private List<BlockItemNode> createVariableDeclsAndInitsForDriver(
			FunctionTypeNode targetFuncType) {
		SequenceNode<VariableDeclarationNode> formals = targetFuncType
				.getParameters();
		List<BlockItemNode> results = new LinkedList<>();

		// create an variable for each formal parameter
		for (VariableDeclarationNode varDecl : formals) {
			VariableDeclarationNode actualDecl;

			// TODO: need a better way: currently for MPI_Comm type
			// parameters,
			// it is always replaced with MPI_COMM_WORLD:
			if (varDecl.getTypeNode().getType()
					.kind() == TypeKind.STRUCTURE_OR_UNION) {
				StructureOrUnionType structType = (StructureOrUnionType) varDecl
						.getTypeNode().getType();

				if (structType.getName().equals(MPI_COMM_TYPE)) {
					results.add(nodeFactory.newVariableDeclarationNode(
							varDecl.getSource(), identifier(varDecl.getName()),
							varDecl.getTypeNode().copy(),
							identifierExpression(MPI_COMM_WORLD)));
					continue;
				}
			}
			actualDecl = varDecl.copy();

			StatementNode havoc;

			results.add(actualDecl);
			// $havoc for the actual parameter declaration:
			havoc = nodeFactory.newExpressionStatementNode(createHavocCall(
					identifierExpression(actualDecl.getName())));
			results.add(havoc);
		}
		return results;
	}

	/* ********************* Processing contract nodes ********************** */
	/**
	 * <p>
	 * <b>Summary: </b> Parses a whole chunk of function contracts, returns a
	 * list of {@link ParsedContractBlock} each of which represents a contract
	 * block in the whole function contracts. A contract block is either the
	 * regular contract block (which specifies sequential properties) or the MPI
	 * collective contract block.
	 * </p>
	 * 
	 * @param contracts
	 *            The body of the whole function contracts
	 * @return A list of {@link ParsedContractBlock} which represents a set of
	 *         contract blocks composes of the whole function contract.
	 */
	private List<ParsedContractBlock> parseFunctionContracts(
			SequenceNode<ContractNode> contracts) {
		List<ParsedContractBlock> results = new LinkedList<>();
		List<ParsedContractBlock> completedResults = new LinkedList<>();
		ParsedContractBlock localMainBlock = new ParsedContractBlock(null, null,
				contracts.getSource());

		parseClausesInBehavior(contracts, localMainBlock);
		for (ContractNode contract : contracts)
			if (contract.contractKind() == ContractKind.MPI_COLLECTIVE)
				results.add(parseMPICollectiveBlock(
						(MPICollectiveBlockNode) contract));
			else if (contract.contractKind() == ContractKind.BEHAVIOR)
				parseClausesInBehavior(((BehaviorNode) contract).getBody(),
						localMainBlock);
		if (localMainBlock.complete())
			completedResults.add(localMainBlock);
		for (ParsedContractBlock block : results)
			if (block.complete())
				completedResults.add(block);
		return completedResults;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Parses a {@link MPICollectiveBlockNode} to a
	 * {@link ParsedContractBlock}.
	 * </p>
	 * 
	 * @param mpiBlockNode
	 *            The {@link MPICollectiveBlockNode} that will be parsed.
	 * @return A {@link ParsedContractBlock} representing an MPI collective
	 *         contract block.
	 */
	private ParsedContractBlock parseMPICollectiveBlock(
			MPICollectiveBlockNode mpiBlockNode) {
		ExpressionNode mpiComm = mpiBlockNode.getMPIComm();
		ParsedContractBlock block = new ParsedContractBlock(mpiComm,
				mpiBlockNode.getCollectiveKind(), mpiBlockNode.getSource());

		parseClausesInBehavior(mpiBlockNode.getBody(), block);
		for (ContractNode contract : mpiBlockNode.getBody())
			if (contract.contractKind() == ContractKind.BEHAVIOR)
				parseClausesInBehavior(((BehaviorNode) contract).getBody(),
						block);
		return block;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Parse contract clauses in a contract behavior. Here
	 * "clause" means a contract clause which specifies a predicate (e.g.
	 * requires, waitsfor). A "behavior" is a lexical block in contracts
	 * specified by a <code>behavior _name</code> contract clause (Such a clause
	 * is classified as a structure clause in this class), specially there is a
	 * default behavior which includes contracts at the outer most lexical
	 * block.
	 * </p>
	 * 
	 * @param contracts
	 *            A {@link SequenceNode} of {@link ContractNode}s in a specific
	 *            contract behavior.
	 * @param currentBlock
	 *            The current {@link ParsedContractBlock} which is either the
	 *            main whole block of function contracts or a contract block
	 *            under an MPI collective title. It will be updated after this
	 *            function returns.
	 */
	private void parseClausesInBehavior(SequenceNode<ContractNode> contracts,
			ParsedContractBlock currentBlock) {
		ExpressionNode assumptions = null;

		// Collects assumptions:
		for (ContractNode contract : contracts)
			if (contract.contractKind() == ContractKind.ASSUMES) {
				ExpressionNode assumes = ((AssumesNode) contract)
						.getPredicate();

				assumptions = assumptions == null
						? assumes
						: nodeFactory.newOperatorNode(assumes.getSource(),
								Operator.LAND, assumptions, assumes);
			}

		ConditionalClauses condClauses = new ConditionalClauses(assumptions);

		// Collects clauses which specifies predicates:
		for (ContractNode contract : contracts) {
			ContractKind kind = contract.contractKind();

			switch (kind) {
				case REQUIRES :
					condClauses.addRequires(
							((RequiresNode) contract).getExpression());
					break;
				case ENSURES :
					condClauses.addEnsures(
							((EnsuresNode) contract).getExpression());
					break;
				case WAITSFOR :
					condClauses.addWaitsfor(
							((WaitsforNode) contract).getArguments());
					break;
				case ASSIGNS_READS : {
					AssignsOrReadsNode assigns = (AssignsOrReadsNode) contract;
					SequenceNode<ExpressionNode> memList;

					if (!assigns.isAssigns())
						break;
					memList = assigns.getMemoryList();
					if (memList.numChildren() <= 0
							|| memList.getSequenceChild(0)
									.expressionKind() != ExpressionKind.NOTHING)
						condClauses.addAssigns(assigns.getMemoryList());
					break;
				}
				default :
					// do nothing.
			}
		}
		currentBlock.addConditionalClauses(condClauses);
	}

	/**
	 * <p>
	 * <b>Pre-condition:</b> The given list of {@link ParsedContractBlock} only
	 * has at most one element that represents a sequential contract block, i.e.
	 * <code>{@link ParsedContractBlock#mpiComm} == null</code>
	 * </p>
	 * <p>
	 * <b>Summary: Factors the sequential contract block (if it exists) out of
	 * the given list, the list will be updated as well.</b>
	 * </p>
	 * <p>
	 * <b>Post-condition:
	 * <code>body.length == pre(body).length - 1 || body.length == pre(body).length</code>
	 * </b>
	 * </p>
	 * 
	 * @param body
	 * @return
	 */
	private ParsedContractBlock factorOutSequentialBlock(
			List<ParsedContractBlock> body) {
		ParsedContractBlock first = body.get(0);

		if (first.mpiComm == null) {
			body.remove(0);
			return first;
		}
		return null;
	}

	/**
	 * Create a (conditional for behavior assumptions) $free call for the given
	 * MPI_Valid expression.
	 * 
	 * @param conditions
	 * @param mpiValidCalls
	 * @return
	 */
	private List<BlockItemNode> createConditionalFreeCalls(
			ExpressionNode conditions,
			List<MPIContractExpressionNode> mpiValids) {
		List<BlockItemNode> result = new LinkedList<>();

		for (MPIContractExpressionNode mpiValid : mpiValids) {
			ExpressionNode ptr = mpiValid.getArgument(0).copy();
			ExpressionNode freeCall = nodeFactory.newFunctionCallNode(
					ptr.getSource(), this.identifierExpression("$free"),
					Arrays.asList(ptr.copy()), null);
			StatementNode stmt = nodeFactory
					.newExpressionStatementNode(freeCall);

			if (conditions != null)
				stmt = nodeFactory.newIfNode(stmt.getSource(),
						conditions.copy(), stmt);
			result.add(stmt);
		}
		return result;
	}

	/**
	 * Creates a set of <code>$mpi_assigns</code> calls for the given
	 * <code>\mpi_region</code> expressions
	 * 
	 * @param expression
	 * @return
	 */
	private ExpressionNode createMPIAssignsCalls(
			MPIContractExpressionNode mpiRegion) {
		ExpressionNode call = nodeFactory.newFunctionCallNode(
				mpiRegion.getSource(), identifierExpression(MPI_ASSIGNS),
				Arrays.asList(mpiRegion.getArgument(0).copy(),
						mpiRegion.getArgument(1).copy(),
						mpiRegion.getArgument(2).copy()),
				null);

		return call;

	}

	/**
	 * Find out all <code>\mpi_valid</code> expressions in the given expression
	 * 
	 * @param expression
	 * @return
	 */
	private List<MPIContractExpressionNode> getMPIValidExpressionNodes(
			ExpressionNode expression) {
		ASTNode astNode = expression;
		List<MPIContractExpressionNode> results = new LinkedList<>();

		do {
			if (astNode instanceof MPIContractExpressionNode) {
				MPIContractExpressionNode mpiCtatExpr = (MPIContractExpressionNode) astNode;

				if (mpiCtatExpr
						.MPIContractExpressionKind() == MPIContractExpressionKind.MPI_VALID) {
					results.add(mpiCtatExpr);
				}
			}
		} while ((astNode = astNode.nextDFS()) != null);
		return results;
	}

	/**
	 * Find out all <code>\valid</code> expressions in the given expression
	 * 
	 * @param expression
	 * @return
	 */
	private Pair<List<OperatorNode>, ExpressionNode> getValidExpressionNodes(
			ExpressionNode expression) {
		ExpressionNode copy = expression.copy();
		ASTNode astNode = copy;
		List<OperatorNode> results = new LinkedList<>();
		OperatorNode opNode;
		ExpressionNode trueExpr = nodeFactory
				.newBooleanConstantNode(expression.getSource(), true);

		do {
			if (astNode instanceof OperatorNode)
				if ((opNode = (OperatorNode) astNode)
						.getOperator() == Operator.VALID) {
					results.add(opNode);
				}
		} while ((astNode = astNode.nextDFS()) != null);

		for (ExpressionNode item : results) {
			ASTNode parent = item.parent();
			int childIdx = item.childIndex();

			item.remove();
			parent.setChild(childIdx, trueExpr.copy());
		}
		return new Pair<>(results, copy);
	}

	/**
	 * Find out all <code>\old</code> expressions in the given expression and
	 * replace them with $value_at expressions:
	 * 
	 * @param expression
	 * @return
	 */
	private ExpressionNode replaceOldExpressionNodes4collective(
			ExpressionNode expression) {
		ExpressionNode copy = expression.copy();
		ASTNode astNode = copy;
		List<OperatorNode> results = new LinkedList<>();
		OperatorNode opNode;
		ExpressionNode valueAtNode;

		do {
			if (astNode instanceof OperatorNode)
				if ((opNode = (OperatorNode) astNode)
						.getOperator() == Operator.OLD) {
					results.add(opNode);
				}
		} while ((astNode = astNode.nextDFS()) != null);

		for (OperatorNode item : results) {
			ASTNode parent = item.parent();
			int childIdx = item.childIndex();

			item.remove();
			valueAtNode = nodeFactory.newValueAtNode(item.getSource(),
					this.functionCall(item.getSource(), COLLATE_GET_STATE,
							Arrays.asList(identifierExpression(
									identifierPrefix + COLLATE_STATE_VAR_PRE))),
					this.identifierExpression(MPI_COMM_RANK_CONST),
					item.getArgument(0).copy());
			parent.setChild(childIdx, valueAtNode);
		}
		return copy;
	}

	/**
	 * <p>
	 * <b>Summary: </b> Replace \old expressions in local contracts:<br>
	 * Given a expression e: for sequential programs (hasMpi == false): <code>
	 * $state state = $get_state();
	 * 
	 * e' = e[\old(a) / $value_at(state, 0, a)]; // where a is an expression
	 * </code> for MPI programs (hasMpi == true): <code>
	 * $collate_state state = $mpi_snaphot(MPI_COMM_WORLD);
	 * 
	 * e' = e[\old(a) / $value_at($collate_get_state(state), $mpi_comm_rank, a)] // where a is an expression
	 * </code>
	 * </p>
	 * 
	 * @param expression
	 * @param hasMpi
	 * @return
	 * @throws SyntaxException
	 */
	private List<BlockItemNode> replaceOldExpressionNodes4Local(
			ExpressionNode expression, boolean hasMpi) throws SyntaxException {
		Source source = expression.getSource();
		VariableDeclarationNode varDecl;
		ASTNode astNode = expression;
		OperatorNode opNode;
		List<OperatorNode> opNodes = new LinkedList<>();
		List<BlockItemNode> results = new LinkedList<>();
		// Function call getting a $state object:
		ExpressionNode getStateCall;
		// Identifiers of $state and process which will be used in $value_at
		// expression:
		ExpressionNode stateIdentiifer, procIndentifier;
		IntegerConstantNode zero = nodeFactory.newIntegerConstantNode(source,
				"0");

		// DFSearch old expressions:
		do {
			if (astNode instanceof OperatorNode)
				if ((opNode = (OperatorNode) astNode)
						.getOperator() == Operator.OLD) {
					opNodes.add(opNode);
				}
		} while ((astNode = astNode.nextDFS()) != null);
		// create state and process identifiers:
		if (hasMpi) {
			getStateCall = createMPISnapshotCall(
					identifierExpression(MPI_COMM_WORLD));
			varDecl = nodeFactory
					.newVariableDeclarationNode(expression.getSource(),
							identifier(TMP_OLD_PREFIX + (tmpOldCounter++)),
							nodeFactory.newTypedefNameNode(
									identifier(COLLATE_STATE), null),
							getStateCall);
			results.add(varDecl);
			stateIdentiifer = functionCall(source, COLLATE_GET_STATE,
					Arrays.asList(identifierExpression(varDecl.getName())));
			varDecl = nodeFactory.newVariableDeclarationNode(
					expression.getSource(),
					identifier(TMP_OLD_PREFIX + (tmpOldCounter++)),
					nodeFactory.newStateTypeNode(source), stateIdentiifer);
			procIndentifier = identifierExpression(MPI_COMM_RANK_CONST);
			results.add(
					createMPICommRankCall(identifierExpression(MPI_COMM_WORLD),
							identifierExpression(MPI_COMM_RANK_CONST)));
		} else {
			getStateCall = functionCall(expression.getSource(), GET_STATE,
					Arrays.asList());
			varDecl = nodeFactory.newVariableDeclarationNode(
					expression.getSource(),
					identifier(TMP_OLD_PREFIX + (tmpOldCounter++)),
					nodeFactory.newStateTypeNode(expression.getSource()),
					getStateCall);
			procIndentifier = zero;
		}
		stateIdentiifer = identifierExpression(varDecl.getName());
		// replace:
		for (OperatorNode item : opNodes) {
			ASTNode parent = item.parent();
			int childIdx = item.childIndex();
			ExpressionNode arg = item.getArgument(0);
			ExpressionNode valueAt;

			item.remove();
			item.getArgument(0).remove();
			valueAt = nodeFactory.newValueAtNode(item.getSource(),
					stateIdentiifer.copy(), procIndentifier.copy(), arg);
			parent.setChild(childIdx, valueAt);
			results.add(varDecl);
		}
		return results;
	}

	/**
	 * <code>
	 * 
	 * void * buf = (char *)malloc(count * $mpi_sizeof(datatype) * sizeof(char));
	 * char tmp0[count * $mpi_sizeof(datatype)];
	 * $copy(buf, tmp0);
	 * </code>
	 * 
	 * @param mpiValid
	 * @return
	 * @throws SyntaxException
	 */
	private List<BlockItemNode> createMallocStatementSequenceForMPIValid(
			MPIContractExpressionNode mpiValid) throws SyntaxException {
		Source source = mpiValid.getSource();
		ExpressionNode buf = mpiValid.getArgument(0);
		ExpressionNode count = mpiValid.getArgument(1);
		ExpressionNode datatype = mpiValid.getArgument(2);
		ExpressionNode countTimesMPISizeof = nodeFactory.newOperatorNode(source,
				Operator.TIMES, Arrays.asList(count.copy(),
						createMPIExtentofCall(datatype.copy())));
		List<BlockItemNode> results = new LinkedList<>();
		TypeNode charType = nodeFactory.newBasicTypeNode(datatype.getSource(),
				BasicTypeKind.CHAR);

		results.add(createMallocStatementWorker(buf.copy(), countTimesMPISizeof,
				charType, source));

		// // $havoc for them:
		ArrayTypeNode arrayTypeNode = nodeFactory.newArrayTypeNode(source,
				charType.copy(), countTimesMPISizeof.copy());
		VariableDeclarationNode tmpHeap = nodeFactory
				.newVariableDeclarationNode(source,
						identifier(TMP_HEAP_PREFIX + (tmpHeapCounter++)),
						arrayTypeNode);
		ExpressionNode copyNode = nodeFactory.newFunctionCallNode(source,
				identifierExpression(COPY),
				Arrays.asList(buf.copy(),
						nodeFactory.newOperatorNode(source, Operator.ADDRESSOF,
								identifierExpression(tmpHeap.getName()))),
				null);

		results.add(createAssumption(
				nodeFactory.newOperatorNode(source, Operator.LT,
						Arrays.asList(
								nodeFactory.newIntegerConstantNode(source, "0"),
								countTimesMPISizeof.copy()))));
		results.add(tmpHeap);
		results.add(nodeFactory.newExpressionStatementNode(copyNode));
		return results;
	}

	/**
	 * Make an array for a \valid expression as the heap object. The type must
	 * be obtained from looking up formal parameters and global variables.
	 * 
	 * @param valid
	 * @param funcDecl
	 * @return
	 * @throws SyntaxException
	 */
	private List<BlockItemNode> createMallocStatementSequenceFoValid(
			OperatorNode valid, FunctionDeclarationNode funcDecl)
			throws SyntaxException {
		Source source = valid.getSource();
		ExpressionNode argument = valid.getArgument(0);
		ExpressionNode count;
		ExpressionNode buf;
		TypeNode referedType, ptrType = null;

		if (argument.expressionKind() == ExpressionKind.OPERATOR) {
			OperatorNode ptrSetExpr = (OperatorNode) argument;
			ExpressionNode range = ptrSetExpr.getArgument(1);

			if (range.expressionKind() == ExpressionKind.REGULAR_RANGE) {
				RegularRangeNode rangeNode = (RegularRangeNode) range;

				count = rangeNode.getHigh();
			} else {
				count = range;
			}
			buf = ptrSetExpr.getArgument(0);
		} else {
			count = nodeFactory.newIntegerConstantNode(source, "0");
			buf = argument;
		}

		if (buf.expressionKind() != ExpressionKind.IDENTIFIER_EXPRESSION)
			throw new CIVLUnimplementedFeatureException(
					"ACSL valid pointer must refer to a formal parameter");
		IdentifierExpressionNode bufId = (IdentifierExpressionNode) buf;

		for (VariableDeclarationNode formal : funcDecl.getTypeNode()
				.getParameters()) {
			if (bufId.getIdentifier().name().equals(formal.getName())) {
				ptrType = formal.getTypeNode();
				break;
			}
		}
		for (VariableDeclarationNode global : globalVarDecls) {
			if (bufId.getIdentifier().name().equals(global.getName())) {
				ptrType = global.getTypeNode();
				break;
			}
		}
		if (ptrType == null)
			throw new CIVLUnimplementedFeatureException(
					"ACSL valid pointer must refer to a formal parameter");
		assert ptrType.kind() == TypeNodeKind.POINTER;
		referedType = ((PointerTypeNode) ptrType).referencedType();

		ArrayTypeNode arrayTypeNode;

		arrayTypeNode = nodeFactory.newArrayTypeNode(buf.getSource(),
				referedType.copy(), count.copy());

		VariableDeclarationNode tmpHeapVar = createTmpHeapVariable(
				buf.getSource(), arrayTypeNode);
		List<BlockItemNode> results = new LinkedList<>();
		ExpressionNode assignExpr = nodeFactory.newOperatorNode(source,
				Operator.ASSIGN, buf.copy(),
				identifierExpression(tmpHeapVar.getName()));

		results.add(tmpHeapVar);
		results.add(nodeFactory.newExpressionStatementNode(assignExpr));
		return results;
	}

	private VariableDeclarationNode createTmpHeapVariable(Source source,
			TypeNode type) {
		return nodeFactory.newVariableDeclarationNode(source,
				identifier(TMP_HEAP_PREFIX + (tmpHeapCounter++)), type);
	}

	private List<BlockItemNode> createMallocStatementSequenceForMPIValid2(
			MPIContractExpressionNode mpiValid) throws SyntaxException {
		Source source = mpiValid.getSource();
		ExpressionNode buf = mpiValid.getArgument(0);
		ExpressionNode count = mpiValid.getArgument(1);
		ExpressionNode datatype = mpiValid.getArgument(2);
		ExpressionNode countTimesMPISizeof = nodeFactory.newOperatorNode(source,
				Operator.TIMES, Arrays.asList(count.copy(),
						createMPIExtentofCall(datatype.copy())));
		List<BlockItemNode> results = new LinkedList<>();

		assert buf.getConvertedType().kind() == TypeKind.POINTER;

		PointerType ptrType = (PointerType) buf.getConvertedType();
		TypeNode referedType;

		if (ptrType.referencedType().kind() != TypeKind.VOID)
			referedType = typeNode(ptrType.referencedType());
		else
			referedType = nodeFactory.newBasicTypeNode(buf.getSource(),
					BasicTypeKind.CHAR);

		ArrayTypeNode arrayTypeNode = nodeFactory.newArrayTypeNode(source,
				referedType.copy(), countTimesMPISizeof.copy());
		VariableDeclarationNode tmpHeap = createTmpHeapVariable(source,
				arrayTypeNode);
		ExpressionNode assignBuf = nodeFactory.newOperatorNode(buf.getSource(),
				Operator.ASSIGN, Arrays.asList(buf.copy(),
						identifierExpression(tmpHeap.getName())));

		results.add(createAssumption(
				nodeFactory.newOperatorNode(source, Operator.LT,
						Arrays.asList(
								nodeFactory.newIntegerConstantNode(source, "0"),
								countTimesMPISizeof.copy()))));
		results.add(tmpHeap);
		results.add(nodeFactory.newExpressionStatementNode(assignBuf));
		return results;
	}

	/**
	 * <code>$mpi_sizeof(datatype)</code>
	 */
	private ExpressionNode createMPIExtentofCall(ExpressionNode datatype) {
		return nodeFactory.newFunctionCallNode(datatype.getSource(),
				identifierExpression(MPI_EXTENTOF), Arrays.asList(datatype),
				null);
	}

	/**
	 * <code>sizeofDatatype(datatype)</code>
	 */
	private ExpressionNode createSizeofDatatype(ExpressionNode datatype) {
		return nodeFactory.newFunctionCallNode(datatype.getSource(),
				identifierExpression(MPI_SIZEOF), Arrays.asList(datatype),
				null);
	}

	/**
	 * Worker which creates malloc statements for
	 * {@link #createIfMallocStatementWorker(IntegerConstantNode, ExpressionNode, ExpressionNode, ExpressionNode, TypeNode, StatementNode, Source)}
	 * 
	 * @param ptr
	 * @param count
	 * @param type
	 * @param source
	 * @return
	 */
	private StatementNode createMallocStatementWorker(ExpressionNode ptr,
			ExpressionNode count, TypeNode type, Source source) {
		Source typeSigSource = newSource(
				count.prettyRepresentation() + " * " + "sizeof("
						+ type.prettyRepresentation() + ")",
				CivlcTokenConstant.OPERATOR);
		Source mallocSource = newSource("malloc", CivlcTokenConstant.CALL);
		Source assignSource = newSource(
				ptr.prettyRepresentation() + "= (T *)malloc( ... )",
				CivlcTokenConstant.RETURN);
		ExpressionNode typeSig = nodeFactory.newOperatorNode(typeSigSource,
				Operator.TIMES, count,
				nodeFactory.newSizeofNode(type.getSource(), type));
		ExpressionNode malloc = nodeFactory.newFunctionCallNode(mallocSource,
				identifierExpression("malloc"), Arrays.asList(typeSig), null);
		ExpressionNode castedMalloc = nodeFactory.newCastNode(
				malloc.getSource(),
				nodeFactory.newPointerTypeNode(type.getSource(), type.copy()),
				malloc);
		ExpressionNode assignExpr = nodeFactory.newOperatorNode(assignSource,
				Operator.ASSIGN, ptr.copy(), castedMalloc);

		return nodeFactory.newExpressionStatementNode(assignExpr);
	}

	private List<BlockItemNode> processConditionalAssignsArgumentNode(
			ExpressionNode condition, List<ExpressionNode> assignsArgs) {
		List<BlockItemNode> results = new LinkedList<>();
		Source source = newSource("assigns ...", CivlcTokenConstant.CONTRACT);

		for (ExpressionNode assignsArg : assignsArgs) {
			StatementNode stmt = nodeFactory.newExpressionStatementNode(
					processAssignsArgumentNodeWorker(assignsArg));

			results.add(stmt);
		}
		if (condition == null)
			return results;
		else {
			StatementNode stmt = nodeFactory.newCompoundStatementNode(source,
					results);

			return Arrays.asList(
					nodeFactory.newIfNode(source, condition.copy(), stmt));
		}
	}

	private ExpressionNode processAssignsArgumentNodeWorker(
			ExpressionNode arg) {
		ExpressionKind kind = arg.expressionKind();

		switch (kind) {
			case OPERATOR : {
				OperatorNode derefNode = (OperatorNode) arg;
				Operator op = derefNode.getOperator();

				if (op == Operator.DEREFERENCE) {
					// For any kind of arguments with the form *(ptr-expr), the
					// assigns clause should be translated as $havoc(ptr-expr):
					return createHavocCall(derefNode.getArgument(0).copy());
				}
				if (op == Operator.SUBSCRIPT) {
					// For any kind of arguments with the form
					// ptr-expr[index], the assign clause should be
					// translated as $havoc(&ptr-expr[index]):
					// TODO: currently not support range:
					ExpressionNode addrDerefNode = nodeFactory.newOperatorNode(
							derefNode.getSource(), Operator.ADDRESSOF,
							derefNode.copy());

					return createHavocCall(addrDerefNode);
				}
				break;
			}
			case MPI_CONTRACT_EXPRESSION : {
				MPIContractExpressionNode mpiConcExpr = (MPIContractExpressionNode) arg;

				assert mpiConcExpr
						.MPIContractExpressionKind() == MPIContractExpressionKind.MPI_REGION;
				return createMPIAssignsCalls(mpiConcExpr);
			}
			default :
				// TODO: do nothing or report an error , what about MemSetNode ?
		}
		throw new CIVLUnimplementedFeatureException(
				"assigns clause with an argument: "
						+ arg.prettyRepresentation());
	}

	/**
	 * Find out variable declarations in the given list of block item nodes, do
	 * $havoc for them.
	 * 
	 * @param root
	 * @return
	 */
	private List<BlockItemNode> havocForGlobalVariables(
			List<BlockItemNode> root) {
		List<BlockItemNode> havocs = new LinkedList<>();

		for (BlockItemNode item : root) {
			if (item.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
				VariableDeclarationNode decl = ((VariableDeclarationNode) item);
				String name = ((VariableDeclarationNode) item).getName();

				globalVarDecls.add(decl);
				havocs.add(nodeFactory.newExpressionStatementNode(
						createHavocCall(identifierExpression(name))));
			}
		}
		return havocs;
	}

	/**
	 * Transform all "MPI_Datatype datatype" appears in the condition to
	 * $mpi_extentof(datatype);
	 * 
	 * @param condition
	 * @return
	 */
	private Pair<List<BlockItemNode>, ExpressionNode> transformMPIDatatype2extentofDatatype(
			ExpressionNode condition) {
		ExpressionNode copy = condition.copy();
		ASTNode node = copy;
		ExpressionNode datatype;
		List<BlockItemNode> results = new LinkedList<>();
		List<Pair<ExpressionNode, ExpressionNode>> item2datatypeSizeof = new LinkedList<>();

		do {
			if (node instanceof MPIContractExpressionNode) {
				MPIContractExpressionNode mpiExpr = (MPIContractExpressionNode) node;

				switch (mpiExpr.MPIContractExpressionKind()) {
					case MPI_EXTENT : {
						VariableDeclarationNode varDecl;

						datatype = mpiExpr.getArgument(0);
						varDecl = createTmpVarForDatatype(datatype.copy(),
								true);
						results.add(varDecl);
						item2datatypeSizeof.add(new Pair<>(mpiExpr,
								identifierExpression(varDecl.getName())));
						break;
					}
					case MPI_EQUALS :
					case MPI_OFFSET :
					case MPI_REGION :
					case MPI_VALID : {
						VariableDeclarationNode varDecl;

						datatype = mpiExpr.getArgument(2);
						varDecl = createTmpVarForDatatype(datatype.copy(),
								false);
						results.add(varDecl);
						item2datatypeSizeof.add(new Pair<>(datatype,
								identifierExpression(varDecl.getName())));
						break;
					}
					default :
						// do nothing
				}
			}
			node = node.nextDFS();
		} while (node != null);
		for (Pair<ExpressionNode, ExpressionNode> item : item2datatypeSizeof) {
			ExpressionNode oldOne = item.left;
			ExpressionNode newOne = item.right;
			ASTNode parent = oldOne.parent();
			int childIdx = oldOne.childIndex();

			oldOne.remove();
			parent.setChild(childIdx, newOne);
		}
		return new Pair<>(results, copy);
	}

	private VariableDeclarationNode createTmpVarForDatatype(
			ExpressionNode datatype, boolean isMPIExtent) {
		TypeNode intNode = nodeFactory.newBasicTypeNode(datatype.getSource(),
				BasicTypeKind.INT);

		if (isMPIExtent)
			return nodeFactory.newVariableDeclarationNode(datatype.getSource(),
					identifier(TMP_EXTENT_PREFIX + (tmpExtentCounter++)),
					intNode, createMPIExtentofCall(datatype));
		else
			return nodeFactory.newVariableDeclarationNode(datatype.getSource(),
					identifier(TMP_EXTENT_PREFIX + (tmpExtentCounter++)),
					intNode, createSizeofDatatype(datatype));
	}

	private SETriple transformLambdaWtRemoteInExtendedQuantifiedExpression(
			ASTNode expr) throws SyntaxException {
		if (expr instanceof ExtendedQuantifiedExpressionNode) {
			return transformLambdaWtRemoteInExtendedQuantifiedExpressionWork(
					(ExtendedQuantifiedExpressionNode) expr);
		}

		List<BlockItemNode> before = new LinkedList<>();
		int numChildren = expr.numChildren();

		for (int i = 0; i < numChildren; i++) {
			ASTNode child = expr.child(i);

			if (child != null) {
				SETriple triple = transformLambdaWtRemoteInExtendedQuantifiedExpression(
						child);

				if (triple != null) {
					before.addAll(triple.getBefore());
					expr.setChild(i, triple.getNode());
				}
			}
		}
		if (!before.isEmpty())
			return new SETriple(before, expr, null);
		return null;
	}

	private ExprTriple transformLambdaWtRemoteInExtendedQuantifiedExpressionWork(
			ExtendedQuantifiedExpressionNode expr) throws SyntaxException {
		ExpressionNode function = expr.function();

		if (function instanceof LambdaNode) {
			LambdaNode lambda = (LambdaNode) function;
			ExpressionNode body = lambda.expression();

			if (hasRemoteExpression(body)) {
				// this is an extended quantified expression on a lambda
				// expression with remote expressions
				// e.g., \sum(0, 5, \lambda int i; \on(i, myCount))
				Type outputType = body.getConvertedType();
				ExpressionNode init;
				VariableDeclarationNode resultVar;
				ExtendedQuantifier quant = expr.extQuantifier();
				VariableDeclarationNode boundVar = lambda.boundVariableList()
						.getSequenceChild(0).getLeft().getSequenceChild(0);
				Operator assignOperator;

				switch (quant) {
					case SUM :
						init = this.integerConstant(0);
						assignOperator = Operator.PLUSEQ;
						break;
					case PROD :
						init = this.integerConstant(1);
						assignOperator = Operator.TIMESEQ;
						break;
					case NUMOF :
					case MAX :
					case MIN :
					default :
						throw new CIVLUnimplementedFeatureException(
								"extended quantifier " + quant,
								expr.getSource());
				}
				resultVar = this.variableDeclaration(
						CONTRACT_VAR_PREFIX + "exquant"
								+ tmpRemoteInLambdaCounter,
						this.typeNode(outputType), init);

				ExpressionNode loopBodyExpr = nodeFactory.newOperatorNode(
						expr.getSource(), assignOperator,
						this.identifierExpression(boundVar.getName()),
						body.copy());

				ExpressionNode domain = nodeFactory.newRegularRangeNode(
						expr.lower().getSource(), expr.lower(), expr.higher());
				StatementNode civlForNode = nodeFactory.newCivlForNode(
						expr.getSource(), false,
						nodeFactory.newForLoopInitializerNode(
								boundVar.getSource(),
								Arrays.asList(boundVar.copy())),
						domain,
						nodeFactory.newExpressionStatementNode(loopBodyExpr),
						null);
				List<BlockItemNode> list = new LinkedList<>();

				list.add(resultVar);
				list.add(civlForNode);
				return new ExprTriple(list,
						this.identifierExpression(boundVar.getName()), null);
			}
		}
		return null;
	}

	private boolean hasRemoteExpression(ASTNode node) {
		if (node instanceof ExpressionNode) {
			ExpressionNode expr = (ExpressionNode) node;

			if (expr.expressionKind() == ExpressionKind.REMOTE_REFERENCE)
				return true;
		}
		for (ASTNode child : node.children()) {
			if (child != null) {
				boolean hasRemote = this
						.hasRemoteExpression((ExpressionNode) child);

				if (hasRemote)
					return true;
			}
		}
		return false;
	}

}
