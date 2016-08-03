package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssumesNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.BehaviorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode.ContractKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.EnsuresNode;
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
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ResultNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.front.IF.CivlcTokenConstant;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.util.IF.Pair;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
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
	private final static String MPI_CONTRACT_ENTERS = "$mpi_contract_enters";

	/**
	 * A CIVL-MPI function identifier:
	 */
	private final static String MPI_CONTRACT_ENTERED = "$mpi_contract_entered";

	/**
	 * A CIVL-MPI function identifier:
	 */
	private final static String MPI_VALID = "$mpi_valid";

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

		ConditionalClauses(ExpressionNode condition) {
			this.condition = condition;
			requiresSet = new LinkedList<>();
			ensuresSet = new LinkedList<>();
			waitsforSet = new LinkedList<>();
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
		 * Returns all requires expressions in this contract behavior
		 * 
		 * @param nodeFactory
		 *            A reference to the {@link NodeFactory}
		 * @return
		 */
		private List<ExpressionNode> getRequires(NodeFactory nodeFactory) {
			if (requiresSet.isEmpty())
				return requiresSet;

			ExpressionNode result = requiresSet.remove(0).copy();

			for (ExpressionNode requires : requiresSet)
				result = nodeFactory.newOperatorNode(requires.getSource(),
						Operator.LAND, result, requires.copy());
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

			ExpressionNode result = ensuresSet.remove(0).copy();

			for (ExpressionNode ensures : ensuresSet)
				result = nodeFactory.newOperatorNode(ensures.getSource(),
						Operator.LAND, result, ensures.copy());
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
		// process function definitions and declarations in source files:
		processedSourceFiles = processSourceFileNodes(sourceFiles);
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
		externalList.add(mainFunction(processedSourceFiles.left, hasMPI));
		newRootNode = nodeFactory.newSequenceNode(null, "TranslationUnit",
				externalList);
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
	 */
	private Pair<FunctionDefinitionNode, List<BlockItemNode>> processSourceFileNodes(
			List<BlockItemNode> sourceFileNodes) {
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
								.add(transformTargetFunction(funcDefi));
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
							.add(transformContractedFunction(funcDecl));
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
	 */
	private FunctionDefinitionNode transformContractedFunction(
			FunctionDeclarationNode funcDecl) {
		CompoundStatementNode body;
		FunctionTypeNode funcTypeNode = funcDecl.getTypeNode();
		List<BlockItemNode> bodyItems = new LinkedList<>();
		Source contractSource = funcDecl.getContract().getSource();
		Source mpiCommRankSource = newSource("int " + MPI_COMM_RANK_CONST + ";",
				CivlcTokenConstant.DECLARATION);
		Source mpiCommSizeSource = newSource("int " + MPI_COMM_SIZE_CONST + ";",
				CivlcTokenConstant.DECLARATION);
		TypeNode intTypeNode;
		List<ParsedContractBlock> parsedContractBlocks;
		ParsedContractBlock localBlock = null;

		// Transform step 1: Inserts assertions for sequential requirements:
		parsedContractBlocks = parseFunctionContracts(funcDecl.getContract());
		localBlock = factorOutSequentialBlock(parsedContractBlocks);
		if (localBlock != null)
			for (ConditionalClauses condClause : localBlock
					.getConditionalClauses())
				for (ExpressionNode requires : condClause
						.getRequires(nodeFactory))
					bodyItems.add(translateConditionalPredicates(false,
							condClause.condition, requires));

		// Transform step 2: Inserts $mpi_comm_rank and $mpi_comm_size:
		intTypeNode = nodeFactory.newBasicTypeNode(
				newSource("int", CivlcTokenConstant.TYPE), BasicTypeKind.INT);
		bodyItems.add(nodeFactory.newVariableDeclarationNode(mpiCommRankSource,
				identifier(MPI_COMM_RANK_CONST), intTypeNode));
		bodyItems.add(nodeFactory.newVariableDeclarationNode(mpiCommSizeSource,
				identifier(MPI_COMM_SIZE_CONST), intTypeNode.copy()));

		// Transform step 3: Takes a snapshot and inserts assertions for
		// requirements of each MPI-collective block:
		for (ParsedContractBlock mpiBlock : parsedContractBlocks)
			bodyItems.addAll(transformCoRequirements4NT(mpiBlock));

		// Transform step 4: Inserts $result declaration:
		bodyItems.add(nodeFactory.newVariableDeclarationNode(contractSource,
				identifier(RESULT),
				funcDecl.getTypeNode().getReturnType().copy()));
		bodyItems.add(createHavocCall(identifierExpression(RESULT)));

		// Transform step 5: Insert assumes for sequential ensurances:
		if (localBlock != null) {
			for (ConditionalClauses condClauses : localBlock
					.getConditionalClauses())
				for (ExpressionNode ensures : condClauses
						.getEnsures(nodeFactory))
					bodyItems.add(translateConditionalPredicates(true,
							condClauses.condition, ensures));
		}

		// Transform step 6: Insert assumes for ensurances of each
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
	 */
	private FunctionDefinitionNode transformTargetFunction(
			FunctionDefinitionNode funcDefi) {
		CompoundStatementNode body;
		ExpressionNode funcIdentifier = identifierExpression(
				funcDefi.getName());
		FunctionTypeNode funcTypeNode = funcDefi.getTypeNode();
		List<ExpressionNode> funcParamIdentfiers = new LinkedList<>();
		List<BlockItemNode> bodyItems = new LinkedList<>();
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
				for (ExpressionNode pred : requires.getRequires(nodeFactory))
					bodyItems.add(translateConditionalPredicates(true,
							requires.condition, pred));

		// Transform step 2: Add $mpi_comm_rank and $mpi_comm_size variables:
		intTypeNode = nodeFactory.newBasicTypeNode(
				newSource("int", CivlcTokenConstant.TYPE), BasicTypeKind.INT);
		bodyItems.add(nodeFactory.newVariableDeclarationNode(mpiCommRankSource,
				identifier(MPI_COMM_RANK_CONST), intTypeNode));
		bodyItems.add(nodeFactory.newVariableDeclarationNode(mpiCommSizeSource,
				identifier(MPI_COMM_SIZE_CONST), intTypeNode.copy()));
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
		bodyItems.add(nodeFactory.newVariableDeclarationNode(contractSource,
				identifier(RESULT),
				funcDefi.getTypeNode().getReturnType().copy(), targetCall));

		// Transform step 8: Inserts "$mpi_contract_entered"s:
		// for (ParsedContractBlock mpiBlock : parsedContractBlocks)
		// for (Pair<ExpressionNode, List<ExpressionNode>> condWaitsforArgs :
		// mpiBlock
		// .getConditionalWaitsfors())
		// bodyItems.add(checkWaitsfors(condWaitsforArgs.left,
		// condWaitsforArgs.right, mpiBlock.mpiComm,
		// mpiBlock.source));

		// Transform step 9: Insert sequential assertions:
		if (localBlock != null)
			for (ConditionalClauses ensures : localBlock
					.getConditionalClauses())
				for (ExpressionNode pred : ensures.getEnsures(nodeFactory))
					bodyItems.add(translateConditionalPredicates(false,
							ensures.condition, pred));

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
	 */
	private List<BlockItemNode> transformCoRequirements4Target(
			ParsedContractBlock mpiBlock, Source mpiCommRankSource,
			Source mpiCommSizeSource) {
		ExpressionNode mpiComm = mpiBlock.mpiComm;
		VariableDeclarationNode collateStateDecl = createCollateStateDeclaration(
				COLLATE_STATE_VAR_PRE, mpiComm);
		StatementNode coAssumeStmt;
		List<BlockItemNode> coAssumesComponents = new LinkedList<>();
		List<BlockItemNode> bodyItems = new LinkedList<>();

		bodyItems.addAll(mpiConstantsInitialization(mpiComm));
		// Add $mpi_valid() calls for \mpi_valid annotations:
		for (ConditionalClauses condClauses : mpiBlock.getConditionalClauses())
			for (ExpressionNode requires : condClauses.getRequires(nodeFactory))
				bodyItems.addAll(createConditionalMPIValidCalls(
						condClauses.condition, requires));
		// take snapshot after do $mpi_valid which elaborates "datatype"s:
		bodyItems.add(collateStateDecl);
		for (ConditionalClauses condClauses : mpiBlock.getConditionalClauses())
			for (ExpressionNode requires : condClauses.getRequires(nodeFactory))
				coAssumesComponents.add(translateConditionalPredicates(true,
						condClauses.condition, requires));
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
	 */
	private List<BlockItemNode> transformCoRequirements4NT(
			ParsedContractBlock mpiBlock) {
		ExpressionNode mpiComm = mpiBlock.mpiComm;
		VariableDeclarationNode collateStateDecl = createCollateStateDeclaration(
				COLLATE_STATE_VAR_PRE, mpiComm);
		List<BlockItemNode> coAssertsComponents = new LinkedList<>();
		List<BlockItemNode> bodyItems = new LinkedList<>();
		StatementNode stmt;

		bodyItems.addAll(mpiConstantsInitialization(mpiComm));
		bodyItems.add(collateStateDecl);
		for (ConditionalClauses condClauses : mpiBlock.getConditionalClauses())
			for (ExpressionNode requires : condClauses.getRequires(nodeFactory))
				coAssertsComponents.add(translateConditionalPredicates(false,
						condClauses.condition, requires));
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
	 */
	private List<BlockItemNode> transformCollectiveEnsures4Target(
			ParsedContractBlock mpiBlock) {
		ExpressionNode mpiComm = mpiBlock.mpiComm;
		VariableDeclarationNode collateStateDecl = createCollateStateDeclaration(
				COLLATE_STATE_VAR_POST, mpiComm);
		StatementNode stmt;
		List<BlockItemNode> bodyItems = new LinkedList<>();

		// $collate_state cp = $collate_snapshot():
		bodyItems.add(collateStateDecl);
		// $when($complete(...)) $with(...) { assert }:
		for (ConditionalClauses condClauses : mpiBlock
				.getConditionalClauses()) {
			StatementNode withStmt;
			List<BlockItemNode> coAssertStmtComponents = new LinkedList<>();

			for (ExpressionNode ensures : condClauses.getEnsures(nodeFactory))
				coAssertStmtComponents.add(translateConditionalPredicates(false,
						condClauses.condition, ensures));
			if (!coAssertStmtComponents.isEmpty()) {
				stmt = nodeFactory.newCompoundStatementNode(mpiBlock.source,
						coAssertStmtComponents);
				withStmt = nodeFactory.newWithNode(stmt.getSource(),
						identifierExpression(collateStateDecl.getName()), stmt);
				bodyItems.add(execAfterComplete(
						identifierExpression(collateStateDecl.getName()),
						withStmt, withStmt.getSource()));
			}
		}
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
		StatementNode stmt;
		List<BlockItemNode> bodyItems = new LinkedList<>();
		VariableDeclarationNode collateStateDecl = createCollateStateDeclaration(
				COLLATE_STATE_VAR_POST, mpiBlock.mpiComm);

		bodyItems.add(collateStateDecl);
		for (ConditionalClauses condClauses : mpiBlock.getConditionalClauses())
			for (ExpressionNode ensures : condClauses.getEnsures(nodeFactory)) {
				stmt = translateEnsurance2Inference(
						identifierExpression(collateStateDecl.getName()),
						condClauses.condition, ensures,
						condClauses.getWaitsfors());
				bodyItems.add(stmt);
			}
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
	 * @return The translated if-then statement.
	 */
	private StatementNode translateConditionalPredicates(boolean isAssume,
			ExpressionNode cond, ExpressionNode preds) {
		StatementNode stmt = isAssume
				? createAssumption(preds)
				: createAssertion(preds);

		// If the condition is null, it doesn't need a
		// branch:
		if (cond != null)
			stmt = nodeFactory.newIfNode(cond.getSource(), cond.copy(), stmt);
		return stmt;
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
	private StatementNode translateEnsurance2Inference(
			ExpressionNode collateStateRef, ExpressionNode condition,
			ExpressionNode ensurance, List<ExpressionNode> waitsforArgs) {
		assert collateStateRef.parent() == null;
		boolean hasGuard = !waitsforArgs.isEmpty();
		StatementNode stmt = createAssumption(ensurance);

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
		if (hasGuard)
			stmt = nodeFactory.newRunNode(stmt.getSource(), stmt);
		return stmt;
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
	 * @return The created $havoc call statement node.
	 */
	private StatementNode createHavocCall(ExpressionNode var) {
		Source source = newSource(
				HAVOC + "(" + var.prettyRepresentation() + ");",
				CivlcTokenConstant.CALL);
		ExpressionNode callIdentifier = identifierExpression(HAVOC);
		ExpressionNode addressOfVar = nodeFactory.newOperatorNode(
				var.getSource(), Operator.ADDRESSOF, var.copy());
		FunctionCallNode call = nodeFactory.newFunctionCallNode(source,
				callIdentifier, Arrays.asList(addressOfVar), null);

		return nodeFactory.newExpressionStatementNode(call);
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
	 * Clumsy declaration creation. Create declaration nodes for :
	 * <ul>
	 * <li>MPI_Comm_size();</li>
	 * <li>MPI_Comm_rank();</li>
	 * <li>MPI_Init();</li>
	 * <li>MPI_Finalize();</li>
	 * <li>$havoc();</li>
	 * <li>$mpi_snapshot();</li>
	 * <li>$mpi_contract_enters();</li>
	 * <li>$mpi_contract_entered();</li>
	 * <li>$collate_complete();</li>
	 * <li>$collate_arrived();</li>
	 * </ul>
	 * 
	 * @return
	 */
	private List<FunctionDeclarationNode> createDeclarationsForUsedFunctions() {
		List<FunctionDeclarationNode> results = new LinkedList<>();
		List<TypeNode> formals;
		FunctionDeclarationNode decl;
		Source intTypeSource = newSource("int ", CivlcTokenConstant.TYPE);
		Source boolTypeSource = newSource("_Bool ", CivlcTokenConstant.TYPE);
		Source rangeTypeSource = newSource("$range ", CivlcTokenConstant.TYPE);
		Source voidSource = newSource("void ", CivlcTokenConstant.TYPE);
		Source ptr2voidSource = newSource("void *", CivlcTokenConstant.TYPE);
		Source ptr2intSource = newSource("int *", CivlcTokenConstant.TYPE);
		Source ptr2charSource = newSource("char *..", CivlcTokenConstant.TYPE);
		TypeNode intTypeNode = nodeFactory.newBasicTypeNode(intTypeSource,
				BasicTypeKind.INT);
		TypeNode boolTypeNode = nodeFactory.newBasicTypeNode(boolTypeSource,
				BasicTypeKind.BOOL);
		TypeNode mpiCommTypeNode = nodeFactory
				.newTypedefNameNode(identifier(MPI_COMM_TYPE), null);
		TypeNode collateStateTypeNode = nodeFactory
				.newTypedefNameNode(identifier(COLLATE_STATE), null);
		// TypeNode rangeTypeNode =
		// nodeFactory.newRangeTypeNode(rangeTypeSource);
		TypeNode rangeTypeNode = nodeFactory.newRangeTypeNode(rangeTypeSource);
		TypeNode ptr2voidNode = nodeFactory.newPointerTypeNode(ptr2voidSource,
				nodeFactory.newVoidTypeNode(voidSource));
		TypeNode ptr2intNode = nodeFactory.newPointerTypeNode(ptr2intSource,
				intTypeNode);
		TypeNode ptr2ptr2ptr2charNode = nodeFactory
				.newPointerTypeNode(ptr2charSource,
						nodeFactory.newPointerTypeNode(ptr2charSource,
								nodeFactory.newPointerTypeNode(ptr2charSource,
										nodeFactory.newBasicTypeNode(
												ptr2charSource,
												BasicTypeKind.CHAR))));

		// MPI_Comm_rank:
		formals = Arrays.asList(mpiCommTypeNode, ptr2intNode);
		results.add(functionDeclarationMaker(MPI_COMM_RANK_CALL, formals,
				intTypeNode.copy(), false,
				"int MPI_Comm_rank(MPI_Comm, int *)"));
		// MPI_Comm_size:
		formals = Arrays.asList(mpiCommTypeNode.copy(), ptr2intNode.copy());
		results.add(functionDeclarationMaker(MPI_COMM_SIZE_CALL, formals,
				intTypeNode.copy(), false,
				"int MPI_Comm_size(MPI_Comm, int *)"));
		// MPI_Init:
		formals = Arrays.asList(ptr2intNode.copy(), ptr2ptr2ptr2charNode);
		results.add(functionDeclarationMaker(MPI_INIT_CALL, formals,
				intTypeNode.copy(), false, "int MPI_Init(int *, char ***)"));
		// MPI_Finalize:
		formals = Arrays.asList();
		results.add(functionDeclarationMaker(MPI_FINALIZE_CALL, formals,
				intTypeNode.copy(), false, "int MPI_Finalize()"));
		// $havoc:
		formals = Arrays.asList(ptr2voidNode.copy());
		decl = functionDeclarationMaker(HAVOC, formals,
				nodeFactory.newVoidTypeNode(voidSource), false,
				"void $havoc(void *)");
		decl.setSystemFunctionSpecifier(true);
		results.add(decl);
		// $mpi_snapshot:
		formals = Arrays.asList(mpiCommTypeNode.copy());
		results.add(functionDeclarationMaker(MPI_SNAPSHOT, formals,
				collateStateTypeNode, false,
				"$collate_state $mpi_snapshot(MPI_Comm )"));
		// $mpi_contract_enters:
		formals = Arrays.asList(mpiCommTypeNode.copy());
		results.add(functionDeclarationMaker(MPI_CONTRACT_ENTERS, formals,
				intTypeNode.copy(), false,
				"int $mpi_contract_enters(MPI_Comm )"));
		// $mpi_contract_entered:
		formals = Arrays.asList(mpiCommTypeNode.copy(), rangeTypeNode);
		results.add(functionDeclarationMaker(MPI_CONTRACT_ENTERED, formals,
				intTypeNode.copy(), true,
				"int $mpi_contract_entered(MPI_Comm, $range)"));
		// $collate_complete:
		formals = Arrays.asList(collateStateTypeNode.copy());
		decl = functionDeclarationMaker(COLLATE_COMPLETE, formals, boolTypeNode,
				false, "_Bool $collate_complete($collate_state)");
		decl.setSystemFunctionSpecifier(true);
		// decl.setPureFunctionSpecifier(true);
		results.add(decl);
		// $collate_arrived:
		formals = Arrays.asList(collateStateTypeNode.copy(),
				rangeTypeNode.copy());
		decl = functionDeclarationMaker(COLLATE_ARRIVED, formals,
				boolTypeNode.copy(), false,
				"_Bool $collate_arrived($collate_state, $range)");
		decl.setSystemFunctionSpecifier(true);
		// decl.setPureFunctionSpecifier(true);
		results.add(decl);
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
			havoc = createHavocCall(identifierExpression(actualDecl.getName()));
			results.add(havoc);
		}
		return results;
	}

	/**
	 * <p>
	 * <b>Summary:</b> A helper method for create function declaration nodes.
	 * </p>
	 * 
	 * @param functionName
	 *            The Name of the function that will be declared
	 * @param formalTypes
	 *            A list of types of formal parameters
	 * @param returnType
	 *            The return type of the declared function
	 * @param hasVariableArguments
	 *            True for set the function to have variant arguments
	 * @param source
	 *            The {@link Source} attahced with the created node
	 * @return
	 */
	private FunctionDeclarationNode functionDeclarationMaker(
			String functionName, List<TypeNode> formalTypes,
			TypeNode returnType, boolean hasVariableArguments, String source) {
		int idcounter = 0;
		String commPrefix = "decl";
		List<VariableDeclarationNode> varDecl = new LinkedList<>();
		SequenceNode<VariableDeclarationNode> varDeclSeq;
		FunctionTypeNode funcType;

		for (TypeNode formalType : formalTypes) {
			varDecl.add(nodeFactory.newVariableDeclarationNode(
					newSource("type id", CivlcTokenConstant.DECLARATION),
					identifier(commPrefix + (idcounter++)), formalType));
		}
		varDeclSeq = nodeFactory.newSequenceNode(
				newSource("formal types", CivlcTokenConstant.SEQUENCE),
				"formal_types", varDecl);
		funcType = nodeFactory.newFunctionTypeNode(
				newSource(source, CivlcTokenConstant.TYPE), returnType,
				varDeclSeq, false);
		funcType.setVariableArgs(hasVariableArguments);
		return nodeFactory.newFunctionDeclarationNode(
				newSource(source, CivlcTokenConstant.DECLARATION),
				identifier(functionName), funcType, null);
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
		Iterator<ParsedContractBlock> iter = body.iterator();

		while (iter.hasNext()) {
			ParsedContractBlock block = iter.next();

			if (block == null) {
				iter.remove();
				return block;
			}
		}
		return null;
	}

	/**
	 * Creates a set of <code>$mpi_valid</code> calls with the given if
	 * conditions for all <code>\mpi_valid</code> expressions in the given
	 * predicate. If there is no any such expression, no call will be created.
	 * If the given if conditions is null, then there is no if branch.
	 * 
	 * @param cond
	 *            The conditional expression
	 * @param predicate
	 *            Thd predication which may contains any <code>\mpi_valid</code>
	 * @return
	 */
	private List<BlockItemNode> createConditionalMPIValidCalls(
			ExpressionNode conditions, ExpressionNode predicate) {
		List<BlockItemNode> stmts = createMPIValidCalls(predicate);
		List<BlockItemNode> result = new LinkedList<>();

		if (!stmts.isEmpty()) {
			if (conditions != null) {
				StatementNode stmt = nodeFactory.newCompoundStatementNode(
						stmts.get(0).getSource(), stmts);

				result.add(nodeFactory.newIfNode(conditions.getSource(),
						conditions.copy(), stmt));
			} else
				return stmts;
		}
		return result;
	}

	/**
	 * Creates a set of <code>$mpi_valid</code> calls for all
	 * <code>\mpi_valid</code> expressions in the given expression
	 * 
	 * @param expression
	 * @return
	 */
	private List<BlockItemNode> createMPIValidCalls(ExpressionNode expression) {
		// TODO: duplicate \mpi_valid expressions will have problems
		List<MPIContractExpressionNode> mpiValids = getMPIValidExpressionNodes(
				expression);
		List<BlockItemNode> stmts = new LinkedList<>();

		for (MPIContractExpressionNode mpiValid : mpiValids) {
			ExpressionNode call = nodeFactory.newFunctionCallNode(
					mpiValid.getSource(), identifierExpression(MPI_VALID),
					Arrays.asList(mpiValid.getArgument(1).copy(),
							mpiValid.getArgument(2).copy()),
					null);
			ExpressionNode lhsCall = nodeFactory.newOperatorNode(
					mpiValid.getSource(), Operator.ASSIGN,
					mpiValid.getArgument(0).copy(), call);

			stmts.add(nodeFactory.newExpressionStatementNode(lhsCall));
		}
		return stmts;
	}

	/**
	 * Find out all <code>\mpi_valid</code> expressions in the given expression
	 * 
	 * @param expression
	 * @return
	 */
	private List<MPIContractExpressionNode> getMPIValidExpressionNodes(
			ExpressionNode expression) {
		ASTNode astNode = expression.copy();
		List<MPIContractExpressionNode> results = new LinkedList<>();

		do {
			if (astNode instanceof MPIContractExpressionNode) {
				MPIContractExpressionNode mpiCtatExpr = (MPIContractExpressionNode) astNode;

				if (mpiCtatExpr
						.MPIContractExpressionKind() == MPIContractExpressionKind.MPI_VALID)
					results.add(mpiCtatExpr);
			}
		} while ((astNode = astNode.nextDFS()) != null);
		return results;
	}

}
