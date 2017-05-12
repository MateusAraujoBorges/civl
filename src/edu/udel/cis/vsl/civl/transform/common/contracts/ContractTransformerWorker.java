package edu.udel.cis.vsl.civl.transform.common.contracts;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.front.IF.CivlcTokenConstant;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.util.IF.Pair;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.transform.IF.ContractTransformer;
import edu.udel.cis.vsl.civl.transform.common.BaseWorker;
import edu.udel.cis.vsl.civl.transform.common.contracts.ContractClauseTransformer.TransformPair;
import edu.udel.cis.vsl.civl.transform.common.contracts.FunctionContractBlock.ConditionalClauses;
import edu.udel.cis.vsl.civl.transform.common.contracts.MPIContractUtilities.TransformConfiguration;

/**
 * This transformer serves for CIVL Contracts mode.
 * 
 * @author ziqingluo
 *
 */
public class ContractTransformerWorker extends BaseWorker {

	/**
	 * MPI_Comm typedef name:
	 */
	private final static String MPI_COMM_TYPE = "MPI_Comm";

	/**
	 * The default MPI communicator identifier:
	 */

	/**
	 * An MPI routine identifier:
	 */
	private final static String MPI_INIT_CALL = "MPI_Init";

	/**
	 * An MPI routine identifier:
	 */
	private final static String MPI_FINALIZE_CALL = "MPI_Finalize";

	/**
	 * Within each function (either non-target : )
	 */

	/**
	 * The name prefix for a driver function
	 */
	private final static String DRIVER_PREFIX = "_driver_";

	/**
	 * A string source for a return statement:
	 */
	private final static String RETURN_RESULT = "return $result;";

	/**
	 * Set of all global variables in source files:
	 */
	private Set<VariableDeclarationNode> globalVarDecls = new HashSet<>();

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

	/**
	 * A int type node
	 */
	private TypeNode intTypeNode;

	TransformConfiguration config;

	public ContractTransformerWorker(ASTFactory astFactory,
			String targetFunctionName, CIVLConfiguration civlConfig) {
		super(ContractTransformer.LONG_NAME, astFactory);
		identifierPrefix = MPIContractUtilities.CIVL_CONTRACT_PREFIX;
		this.targetFunctionName = targetFunctionName;
		intTypeNode = nodeFactory.newBasicTypeNode(
				newSource("int", CivlcTokenConstant.TYPE), BasicTypeKind.INT);
		config = MPIContractUtilities.getTransformConfiguration();
		this.mpiCommRankSource = this.newSource("$mpi_comm_rank",
				CivlcTokenConstant.IDENTIFIER);
		this.mpiCommSizeSource = this.newSource("$mpi_comm_size",
				CivlcTokenConstant.IDENTIFIER);
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
		/*
		 * process source file: For all functions f in source file, if f is the
		 * target function, transform f with "transformTargetFunction"; Else if
		 * f is contracted, transform f with "transformAnnotatedFunction"; Else,
		 * keep f unchanged (f might be executed with it's definition or may
		 * never be used).
		 */
		for (BlockItemNode child : root) {
			if (child == null || child.getSource() == null)
				continue;
			sourceFileName = child.getSource().getFirstToken().getSourceFile()
					.getName();
			if (sourceFileName.endsWith(".c"))
				sourceFiles.add(child);
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
		processedSourceFiles.left.remove();
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
	/* ******************* Package private methods: ******************** */
	/**
	 * @param type
	 *            a {@link Type} instance
	 * @param source
	 *            {@link Source} will associate to the returned node
	 * @return A {@link TypeNode} of the given type.
	 */
	TypeNode typeNode(Type type, Source source) {
		return super.typeNode(source, type);
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
	 * For functions with contracts but are not the target function, replacing a
	 * new deductive definition for them; for the target function, create a
	 * driver function for it.
	 * 
	 * @param sourceFileNodes
	 * @return A pair of a {@link FunctionDefinitionNode} which represents the
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
				// the target function:
				if (funcDecl.isDefinition()) {
					FunctionDefinitionNode funcDefi = (FunctionDefinitionNode) funcDecl;

					if (funcDefi.getName().equals(targetFunctionName)) {
						// Keep the original function definition of the
						// target function:
						newSourceFileNodes.add(funcDefi);
						if (funcDefi.getContract() != null) {
							newSourceFileNodes.add(
									transformTargetFunction(funcDefi, hasMpi));
							target = funcDefi;
							target.remove();
							target.getContract().remove();
							continue;
						} else
							throw new CIVLSyntaxException(
									"No contracts specified for the target function");
					}
				} else
					newSourceFileNodes.add(funcDecl);
				// If the function declaration is contracted, create a
				// harness definition for it, it's original definition will not
				// be added into the new source file components if it is defined
				// in source files:
				// TODO: think about both definition and declaration have
				// contracts.
				if (funcDecl.getContract() != null) {
					FunctionDefinitionNode defiOfThis;
					TypeNode funcDeclTypeNode = funcDecl.getTypeNode();

					if (funcDeclTypeNode
							.kind() == TypeNode.TypeNodeKind.FUNCTION)
						newSourceFileNodes.add(transformCalleeFunction(funcDecl,
								(FunctionTypeNode) funcDeclTypeNode, hasMpi));
					if ((defiOfThis = funcDecl.getEntity()
							.getDefinition()) != null)
						defiOfThis.remove();
				}
			} else {
				child.remove();
				newSourceFileNodes.add(child);
				continue;
			}
		}
		if (target == null)
			throw new CIVLSyntaxException("Target function: "
					+ this.targetFunctionName + " not exist!");
		return new Pair<>(target, newSourceFileNodes);
	}

	/**
	 * <p>
	 * Transform a non-target contracted function into a deductive executable
	 * form.
	 * </p>
	 * 
	 * <p>
	 * The body of a non-target contracted function f will be added or replaced
	 * its definition with: <code>
	 * f () {
	 *   assert ( seq-requires );
	 *   cp = snapshot();
	 *   $run $when($collate_arrived(cp, args .. )) $with(cp) 
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
	 * </code>
	 * </p>
	 * 
	 * @param funcDecl
	 *            The {@link FunctionDeclarationNode} of the transformed
	 *            function. It's original body will be removed.
	 * @return
	 * @throws SyntaxException
	 */
	private FunctionDefinitionNode transformCalleeFunction(
			FunctionDeclarationNode funcDecl, FunctionTypeNode funcTypeNode,
			boolean hasMpi) throws SyntaxException {
		CompoundStatementNode body;
		Source contractSource = funcDecl.getContract().getSource();
		List<FunctionContractBlock> contractBlocks;
		ContractClauseTransformer clauseTransformer = new ContractClauseTransformer(
				astFactory);
		/*
		 * Requirements (including assigns) of callees will be transformed to
		 * assertions
		 */
		List<BlockItemNode> transformedRequirements = new LinkedList<>();
		/* Ensurances of callees will be transformed to assumptions */
		List<BlockItemNode> transformedEnsurances = new LinkedList<>();
		FunctionContractBlock localBlock = null;

		contractBlocks = FunctionContractBlock
				.parseContract(funcDecl.getContract(), nodeFactory);
		// callee shall not do allocation:
		config.setAlloc4Valid(false);
		if (contractBlocks.get(0).isSequentialBlock())
			localBlock = contractBlocks.remove(0);
		if (localBlock != null) {
			/*
			 * Transform sequential contracts:
			 */
			config.setInMPIBlock(false);
			for (ConditionalClauses condClause : localBlock
					.getConditionalClauses()) {
				ExpressionNode requires = condClause.getRequires(nodeFactory);
				ExpressionNode ensures = condClause.getEnsures(nodeFactory);
				StatementNode assumptions;
				List<BlockItemNode> tmpContainer = new LinkedList<>();
				Pair<List<BlockItemNode>, ExpressionNode> sideEffects;

				if (requires != null) {
					config.setIgnoreOld(true);
					config.setNoResult(true);
					config.setAlloc4Valid(false);
					sideEffects = clauseTransformer
							.ACSLSideEffectRemoving(requires, config);
					tmpContainer.addAll(sideEffects.left);
					requires = clauseTransformer
							.ACSLPrimitives2CIVLC(sideEffects.right, config);
					tmpContainer
							.add(clauseTransformer.createAssertion(requires));
				}
				tmpContainer.addAll(clauseTransformer
						.transformAssignsClause(condClause.getAssignsArgs()));
				if (condClause.condition != null) {
					ExpressionNode cond = condClause.condition;
					StatementNode compound = nodeFactory
							.newCompoundStatementNode(
									tmpContainer.get(0).getSource(),
									tmpContainer);

					transformedRequirements.add(nodeFactory.newIfNode(
							cond.getSource(), cond.copy(), compound));
				}
				if (ensures != null) {
					tmpContainer.clear();
					config.setIgnoreOld(false);
					config.setNoResult(false);
					config.setAlloc4Valid(false);
					sideEffects = clauseTransformer
							.ACSLSideEffectRemoving(ensures, config);
					tmpContainer.addAll(sideEffects.left);
					ensures = clauseTransformer
							.ACSLPrimitives2CIVLC(sideEffects.right, config);
					assumptions = clauseTransformer.createAssumption(ensures);
					tmpContainer.add(assumptions);
					if (condClause.condition != null) {
						StatementNode compountStmt = nodeFactory
								.newCompoundStatementNode(ensures.getSource(),
										tmpContainer);

						transformedEnsurances.add(nodeFactory.newIfNode(
								condClause.condition.getSource(),
								condClause.condition.copy(), compountStmt));
					}
				}
			}
		}

		/* inserts $mpi_comm_rank and $mpi_comm_size: */
		transformedRequirements
				.add(nodeFactory.newVariableDeclarationNode(mpiCommRankSource,
						identifier(MPIContractUtilities.MPI_COMM_RANK_CONST),
						intTypeNode.copy()));
		transformedRequirements
				.add(nodeFactory.newVariableDeclarationNode(mpiCommSizeSource,
						identifier(MPIContractUtilities.MPI_COMM_SIZE_CONST),
						intTypeNode.copy()));

		config.setInMPIBlock(true);
		config.setRunWithArrived(true);
		for (FunctionContractBlock mpiBlock : contractBlocks) {
			TransformPair transformedBlockPair = clauseTransformer
					.transformMPICollectiveBlock4Callee(mpiBlock, config);

			transformedRequirements.addAll(transformedBlockPair.requirements);
			transformedEnsurances.addAll(transformedBlockPair.ensurances);
		}
		// Unsnapshots for preState and postState:
		for (FunctionContractBlock mpiBlock : contractBlocks) {
			StatementNode unsnapshotPre = nodeFactory
					.newExpressionStatementNode(createMPIUnsnapshotCall(
							mpiBlock.getMPIComm().copy(), identifierExpression(
									MPIContractUtilities.COLLATE_PRE_STATE)));
			StatementNode unsnapshotPost = nodeFactory
					.newExpressionStatementNode(createMPIUnsnapshotCall(
							mpiBlock.getMPIComm().copy(), identifierExpression(
									MPIContractUtilities.COLLATE_POST_STATE)));

			transformedEnsurances.add(unsnapshotPre);
			transformedEnsurances.add(unsnapshotPost);
		}

		List<BlockItemNode> bodyItems = new LinkedList<>();
		boolean returnVoid = false;

		bodyItems.addAll(transformedRequirements);
		returnVoid = isVoidType(funcTypeNode.getReturnType().getType());
		if (!returnVoid) {
			bodyItems.add(nodeFactory.newVariableDeclarationNode(contractSource,
					identifier(MPIContractUtilities.ACSL_RESULT_VAR),
					funcTypeNode.getReturnType().copy()));
			bodyItems
					.add(nodeFactory.newExpressionStatementNode(createHavocCall(
							identifierExpression(
									MPIContractUtilities.ACSL_RESULT_VAR),
							nodeFactory)));
		}
		bodyItems.addAll(transformedEnsurances);
		if (!returnVoid)
			bodyItems.add(nodeFactory.newReturnNode(
					newSource(RETURN_RESULT, CivlcTokenConstant.RETURN),
					identifierExpression(
							MPIContractUtilities.ACSL_RESULT_VAR)));
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
		String driverName = DRIVER_PREFIX + funcDefi.getName();
		Source contractSource = funcDefi.getContract().getSource();
		Source driverSource = newSource(driverName,
				CivlcTokenConstant.FUNCTION_DEFINITION);
		ContractClauseTransformer clauseTransformer = new ContractClauseTransformer(
				astFactory);

		List<BlockItemNode> requirements = new LinkedList<>();
		List<BlockItemNode> ensurances = new LinkedList<>();
		List<FunctionContractBlock> parsedContractBlocks = FunctionContractBlock
				.parseContract(funcDefi.getContract(), nodeFactory);
		FunctionContractBlock localBlock = null;
		TransformConfiguration config = MPIContractUtilities
				.getTransformConfiguration();

		if (parsedContractBlocks.get(0).isSequentialBlock())
			localBlock = parsedContractBlocks.remove(0);
		config.setInMPIBlock(true);
		if (localBlock != null) {
			// transform local contracts:
			for (ConditionalClauses condClause : localBlock
					.getConditionalClauses()) {
				ExpressionNode requires, ensures;
				List<BlockItemNode> tmpContainer = new LinkedList<>();

				requires = condClause.getRequires(nodeFactory);
				if (requires != null) {
					StatementNode assumptions;
					Pair<List<BlockItemNode>, ExpressionNode> sideEffects;

					config.setIgnoreOld(true);
					config.setNoResult(true);
					config.setAlloc4Valid(true);
					sideEffects = clauseTransformer
							.ACSLSideEffectRemoving(requires, config);
					tmpContainer.addAll(sideEffects.left);
					requires = clauseTransformer
							.ACSLPrimitives2CIVLC(sideEffects.right, config);
					assumptions = clauseTransformer.createAssumption(requires);
					tmpContainer.add(assumptions);
				}
				tmpContainer.addAll(clauseTransformer
						.transformAssignsClause(condClause.getAssignsArgs()));
				if (condClause.condition != null) {
					StatementNode compound = nodeFactory
							.newCompoundStatementNode(requires.getSource(),
									tmpContainer);

					requirements.add(nodeFactory.newIfNode(
							condClause.condition.getSource(),
							condClause.condition, compound));
				} else
					requirements.addAll(tmpContainer);
				ensures = condClause.getEnsures(nodeFactory);
				if (ensures != null) {
					StatementNode assertion;
					Pair<List<BlockItemNode>, ExpressionNode> sideEffects;

					config.setIgnoreOld(false);
					config.setNoResult(false);
					config.setAlloc4Valid(false);
					sideEffects = clauseTransformer
							.ACSLSideEffectRemoving(ensures, config);
					ensurances.addAll(sideEffects.left);
					ensures = clauseTransformer
							.ACSLPrimitives2CIVLC(sideEffects.right, config);
					assertion = clauseTransformer.createAssertion(ensures);
					if (condClause.condition != null)
						assertion = nodeFactory.newIfNode(
								condClause.condition.getSource(),
								condClause.condition, assertion);
					ensurances.add(assertion);
				}
			}
		}

		// add $mpi_comm_rank and $mpi_comm_size variables:
		requirements
				.add(nodeFactory.newVariableDeclarationNode(mpiCommRankSource,
						identifier(MPIContractUtilities.MPI_COMM_RANK_CONST),
						intTypeNode.copy()));
		requirements
				.add(nodeFactory.newVariableDeclarationNode(mpiCommSizeSource,
						identifier(MPIContractUtilities.MPI_COMM_SIZE_CONST),
						intTypeNode.copy()));
		// for each MPI block, translate requirements:
		config.setInMPIBlock(true);
		config.setWithComplete(true);
		for (FunctionContractBlock mpiBlock : parsedContractBlocks) {
			TransformPair pair = clauseTransformer
					.transformMPICollectiveBlock4Target(mpiBlock, config);

			requirements.addAll(pair.requirements);
			ensurances.addAll(pair.ensurances);
		}
		// Unsnapshots for pre- and post-:
		for (FunctionContractBlock mpiBlock : parsedContractBlocks) {
			ensurances.add(nodeFactory.newExpressionStatementNode(
					createMPIUnsnapshotCall(mpiBlock.getMPIComm().copy(),
							identifierExpression(
									MPIContractUtilities.COLLATE_PRE_STATE))));
			ensurances.add(nodeFactory.newExpressionStatementNode(
					createMPIUnsnapshotCall(mpiBlock.getMPIComm().copy(),
							identifierExpression(
									MPIContractUtilities.COLLATE_POST_STATE))));
		}

		List<BlockItemNode> driverComponents = new LinkedList<>();
		ExpressionNode targetCall;
		ExpressionNode funcIdentifier = identifierExpression(
				funcDefi.getName());
		FunctionTypeNode funcTypeNode = funcDefi.getTypeNode();
		List<ExpressionNode> funcParamIdentfiers = new LinkedList<>();

		for (VariableDeclarationNode param : funcTypeNode.getParameters())
			funcParamIdentfiers
					.add(identifierExpression(param.getIdentifier().name()));
		targetCall = nodeFactory.newFunctionCallNode(driverSource,
				funcIdentifier.copy(), funcParamIdentfiers, null);

		// Create variable declarations which are actual parameters of the
		// target function:
		driverComponents
				.addAll(createVariableDeclsAndInitsForDriver(funcTypeNode));
		driverComponents.addAll(requirements);
		if (!isVoidType(funcTypeNode.getReturnType().getType()))
			driverComponents.add(nodeFactory.newVariableDeclarationNode(
					contractSource,
					identifier(MPIContractUtilities.ACSL_RESULT_VAR),
					funcDefi.getTypeNode().getReturnType().copy(), targetCall));
		else
			driverComponents
					.add(nodeFactory.newExpressionStatementNode(targetCall));
		driverComponents.addAll(ensurances);
		body = nodeFactory.newCompoundStatementNode(driverSource,
				driverComponents);
		funcTypeNode = nodeFactory.newFunctionTypeNode(funcTypeNode.getSource(),
				funcTypeNode.getReturnType().copy(),
				nodeFactory.newSequenceNode(
						funcTypeNode.getParameters().getSource(),
						"contract_driver_parameters", Arrays.asList()),
				funcTypeNode.hasIdentifierList());
		return nodeFactory.newFunctionDefinitionNode(driverSource,
				identifier(driverName), funcTypeNode.copy(), null, body);
	}

	/*
	 * ************************* Utility methods ****************************
	 */

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
	private ExpressionNode createMPIUnsnapshotCall(ExpressionNode mpiComm,
			ExpressionNode collateStateRef) {
		Source source = newSource(MPIContractUtilities.MPI_UNSNAPSHOT,
				CivlcTokenConstant.CALL);
		ExpressionNode callIdentifier = identifierExpression(
				MPIContractUtilities.MPI_UNSNAPSHOT);
		FunctionCallNode call = nodeFactory.newFunctionCallNode(source,
				callIdentifier, Arrays.asList(mpiComm, collateStateRef), null);

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
	 * <p>
	 * <b>Summary: </b> Creates an $havoc function call:<code>
	 * $mpi_snapshot(&var);</code>
	 * </p>
	 * 
	 * @param var
	 *            An {@link ExpressionNode} representing an variable.
	 * @return The created $havoc call expression node.
	 */
	private ExpressionNode createHavocCall(ExpressionNode var,
			NodeFactory nodeFactory) {
		Source source = var.getSource();
		ExpressionNode callIdentifier = identifierExpression(source,
				MPIContractUtilities.HAVOC);
		ExpressionNode addressOfVar = nodeFactory.newOperatorNode(
				var.getSource(), Operator.ADDRESSOF, var.copy());
		FunctionCallNode call = nodeFactory.newFunctionCallNode(source,
				callIdentifier, Arrays.asList(addressOfVar), null);

		return call;
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
							varDecl.getTypeNode().copy(), identifierExpression(
									MPIContractUtilities.MPI_COMM_WORLD)));
					continue;
				}
			}
			actualDecl = varDecl.copy();

			StatementNode havoc;

			results.add(actualDecl);
			// $havoc for the actual parameter declaration:
			havoc = nodeFactory.newExpressionStatementNode(createHavocCall(
					identifierExpression(actualDecl.getName()), nodeFactory));
			results.add(havoc);
		}
		return results;
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
				havocs.add(
						nodeFactory.newExpressionStatementNode(createHavocCall(
								identifierExpression(name), nodeFactory)));
			}
		}
		return havocs;
	}
}
