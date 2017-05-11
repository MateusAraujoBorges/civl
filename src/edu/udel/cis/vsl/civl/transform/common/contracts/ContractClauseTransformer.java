package edu.udel.cis.vsl.civl.transform.common.contracts;

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPICollectiveBlockNode.MPICommunicatorMode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractExpressionNode.MPIContractExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.EnumerationConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.RegularRangeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.RemoteOnExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ResultNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.DeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.util.IF.Pair;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.transform.common.BaseWorker;
import edu.udel.cis.vsl.civl.transform.common.contracts.FunctionContractBlock.ConditionalClauses;
import edu.udel.cis.vsl.civl.transform.common.contracts.MPIContractUtilities.TransformConfiguration;
class ContractClauseTransformer {

	private int tmpHeapCounter = 0;

	private int tmpAssignCounter = 0;

	private int tmpExtentCounter = 0;

	Map<String, String> datatype2counter;

	LinkedList<ExpressionNode> sideEffectConditions;

	/**
	 * A reference to an instance of {@link NodeFactory}
	 */
	private NodeFactory nodeFactory;

	class TransformPair {
		List<BlockItemNode> requirements;
		List<BlockItemNode> ensurances;

		TransformPair(List<BlockItemNode> preNodes,
				List<BlockItemNode> postNodes) {
			this.requirements = preNodes;
			this.ensurances = postNodes;
		}
	}

	ContractClauseTransformer(ASTFactory astFactory) {
		this.nodeFactory = astFactory.getNodeFactory();
		this.datatype2counter = new HashMap<>();
		this.sideEffectConditions = new LinkedList<>();
	}

	/**
	 * Replace ACSL constructs to CIVL-C primitives
	 */
	ExpressionNode ACSLPrimitives2CIVLC(ExpressionNode predicate,
			TransformConfiguration config) throws SyntaxException {
		predicate = old2ValueAt(predicate, null, config);
		return on2ValueAt(predicate, null, config);
	}

	ExpressionNode ACSLPrimitives2CIVLC(ExpressionNode predicate,
			ExpressionNode preCollateState, TransformConfiguration config)
			throws SyntaxException {
		ExpressionNode state = createCollateGetStateCall(preCollateState,
				predicate.getSource());

		predicate = on2ValueAt(predicate, null, config);
		predicate = old2ValueAt(predicate, state, config);
		return result2intermediate(predicate, config);
	}

	Pair<List<BlockItemNode>, ExpressionNode> ACSLSideEffectRemoving(
			ExpressionNode predicate, TransformConfiguration config)
			throws SyntaxException {
		Pair<List<BlockItemNode>, ExpressionNode> result = mpiExtent2intermediate(
				predicate);

		if (config.alloc4Valid()) {
			Pair<List<BlockItemNode>, ExpressionNode> subResult = allocation4Valids(
					result.right, config);

			result.left.addAll(subResult.left);
			result.right = subResult.right;
		}
		return result;
	}

	TransformPair transformMPICollectiveBlock4Callee(
			FunctionContractBlock mpiBlock, TransformConfiguration config)
			throws SyntaxException {
		LinkedList<BlockItemNode> requirements = new LinkedList<>();
		LinkedList<BlockItemNode> ensurances = new LinkedList<>();
		ExpressionNode mpiComm = mpiBlock.getMPIComm();
		Source source = mpiComm.getSource();
		VariableDeclarationNode preStateDecl = createCollateStateInitializer(
				MPIContractUtilities.COLLATE_PRE_STATE, mpiComm);
		ExpressionNode preState = nodeFactory.newIdentifierExpressionNode(
				source,
				nodeFactory.newIdentifierNode(source, preStateDecl.getName()));
		VariableDeclarationNode postStateDecl = createCollateStateInitializer(
				MPIContractUtilities.COLLATE_POST_STATE, mpiComm);
		ExpressionNode postState = nodeFactory.newIdentifierExpressionNode(
				source,
				nodeFactory.newIdentifierNode(source, postStateDecl.getName()));

		requirements.addAll(mpiConstantsInitialization(mpiComm));
		requirements.add(preStateDecl);
		ensurances.add(postStateDecl);

		for (ConditionalClauses condClause : mpiBlock.getConditionalClauses()) {
			ExpressionNode requires = condClause.getRequires(nodeFactory);
			ExpressionNode ensures = condClause.getEnsures(nodeFactory);
			Pair<List<BlockItemNode>, ExpressionNode> sideEffects;

			if (requires != null) {
				config.setIgnoreOld(true);
				config.setNoResult(true);
				config.setAlloc4Valid(false);
				sideEffects = ACSLSideEffectRemoving(requires, config);
				requirements.addAll(sideEffects.left);
				requires = ACSLPrimitives2CIVLC(sideEffects.right, preState,
						config);
				requirements.addAll(
						transformClause2Checking(condClause.condition, requires,
								preState, condClause.getWaitsfors(), config));
			}
			requirements.addAll(
					transformAssignsClause(condClause.getAssignsArgs()));
			if (ensures != null) {
				config.setIgnoreOld(false);
				config.setNoResult(false);
				config.setAlloc4Valid(false);
				sideEffects = ACSLSideEffectRemoving(ensures, config);
				ensures = ACSLPrimitives2CIVLC(sideEffects.right, preState,
						config);
				ensurances.addAll(sideEffects.left);
				ensurances.addAll(transformClause2Assumption(
						condClause.condition, ensures, postState,
						condClause.getWaitsfors(), config));
			}
		}
		return new TransformPair(requirements, ensurances);
	}

	TransformPair transformMPICollectiveBlock4Target(
			FunctionContractBlock mpiBlock, TransformConfiguration config)
			throws SyntaxException {
		LinkedList<BlockItemNode> requirements = new LinkedList<>();
		LinkedList<BlockItemNode> ensurances = new LinkedList<>();
		ExpressionNode mpiComm = mpiBlock.getMPIComm();
		Source source = mpiComm.getSource();
		VariableDeclarationNode preStateDecl = createCollateStateInitializer(
				MPIContractUtilities.COLLATE_PRE_STATE, mpiComm);
		ExpressionNode preState = nodeFactory.newIdentifierExpressionNode(
				source,
				nodeFactory.newIdentifierNode(source, preStateDecl.getName()));
		VariableDeclarationNode postStateDecl = createCollateStateInitializer(
				MPIContractUtilities.COLLATE_POST_STATE, mpiComm);
		ExpressionNode postState = nodeFactory.newIdentifierExpressionNode(
				source,
				nodeFactory.newIdentifierNode(source, postStateDecl.getName()));
		Pair<List<BlockItemNode>, ExpressionNode> sideEffects;

		requirements.addAll(mpiConstantsInitialization(mpiComm));
		requirements.add(preStateDecl);
		ensurances.add(postStateDecl);
		for (ConditionalClauses condClause : mpiBlock.getConditionalClauses()) {
			ExpressionNode requires = condClause.getRequires(nodeFactory);
			ExpressionNode ensures = condClause.getEnsures(nodeFactory);

			if (requires != null) {
				config.setIgnoreOld(true);
				config.setNoResult(true);
				config.setAlloc4Valid(true);
				sideEffects = ACSLSideEffectRemoving(requires, config);
				requirements.addAll(0, sideEffects.left);
				requires = ACSLPrimitives2CIVLC(sideEffects.right, preState,
						config);
				requirements.addAll(transformClause2Assumption(
						condClause.condition, requires, preState,
						condClause.getWaitsfors(), config));
				sideEffectConditions.clear();
			}
			if (ensures != null) {
				// TODO: How check assigns ?
				config.setIgnoreOld(false);
				config.setNoResult(false);
				config.setAlloc4Valid(false);
				sideEffects = ACSLSideEffectRemoving(ensures, config);
				ensurances.addAll(0, sideEffects.left);
				ensures = ACSLPrimitives2CIVLC(sideEffects.right, preState,
						config);
				ensurances.addAll(transformClause2Checking(condClause.condition,
						ensures, postState, condClause.getWaitsfors(), config));
			}
		}
		requirements.add(nodeFactory
				.newExpressionStatementNode(createMPIBarrier(mpiComm)));
		ensurances.addLast(nodeFactory.newExpressionStatementNode(
				createMPICommEmptyCall(mpiComm, mpiBlock.getKind())));
		return new TransformPair(requirements, ensurances);
	}

	List<BlockItemNode> transformClause2Checking(ExpressionNode condition,
			ExpressionNode predicate, ExpressionNode collateState,
			List<ExpressionNode> arrivends, TransformConfiguration config)
			throws SyntaxException {
		StatementNode assertion = createAssertion(predicate.copy());

		assertion = withStatementWrapper(assertion, collateState, arrivends,
				config);
		// conditional transformation:
		if (condition != null)
			assertion = nodeFactory.newIfNode(condition.getSource(),
					condition.copy(), assertion);

		List<BlockItemNode> results = new LinkedList<>();

		// elaborate waited arguments:
		if (arrivends != null)
			for (ExpressionNode arrivend : arrivends) {
				if (arrivend.expressionKind() == ExpressionKind.REGULAR_RANGE) {
					RegularRangeNode range = (RegularRangeNode) arrivend;

					results.add(createElaborateFor(range.getLow()));
					results.add(createElaborateFor(range.getHigh()));
				} else
					results.add(createElaborateFor(arrivend));
			}
		results.add(assertion);
		return results;
	}

	/**
	 * Transform a predicate specified by a contract clause into assumptions A.
	 * Each a in A is a condition that will be assumed hold. The returned set of
	 * {@link BlockItemNode} can be any kind of nodes serving such a assuming
	 * purpose, they can be declarations of temporary variables, CIVL-C $assume
	 * statements or assignments ( which is a direct way to assume some variable
	 * has some value), etc.
	 * 
	 * @param condition
	 *            The condition or assumption under where the predicate should
	 *            hold.
	 * @param predicate
	 *            The predicate expression
	 * @param evalKind
	 *            The {@link CollectiveEvaluationKind} for this predicate.
	 * @param collateState
	 *            The reference to a collate state, it's significant only when
	 *            the 'evalKind' is chosen
	 *            {@link CollectiveEvaluationKind#ARRIVED_WITH} or
	 *            {@link CollectiveEvaluationKind#COMPLETE_WITH}.
	 * @param arriveds
	 *            A set of places of processes, it's significant only when the
	 *            'evalKind' is chosen
	 *            {@link CollectiveEvaluationKind#ARRIVED_WITH}.
	 * @return
	 */
	List<BlockItemNode> transformClause2Assumption(ExpressionNode condition,
			ExpressionNode predicate, ExpressionNode collateState,
			List<ExpressionNode> arrivends, TransformConfiguration config) {
		StatementNode assumes = createAssumption(predicate.copy());

		if (!sideEffectConditions.isEmpty()) {
			ExpressionNode sfconds = sideEffectConditions.remove().copy();
			StatementNode sfcondsDischarge;

			for (ExpressionNode sfcond : sideEffectConditions)
				sfconds = nodeFactory.newOperatorNode(sfcond.getSource(),
						Operator.LAND, Arrays.asList(sfcond.copy(), sfconds));
			sfcondsDischarge = createAssertion(nodeFactory.newOperatorNode(
					sfconds.getSource(), Operator.IMPLIES,
					Arrays.asList(predicate.copy(), sfconds)));
			assumes = nodeFactory.newCompoundStatementNode(assumes.getSource(),
					Arrays.asList(sfcondsDischarge, assumes));
		}

		assumes = withStatementWrapper(assumes, collateState, arrivends,
				config);
		// conditional transformation:
		if (condition != null)
			assumes = nodeFactory.newIfNode(condition.getSource(),
					condition.copy(), assumes);

		List<BlockItemNode> results = new LinkedList<>();

		// elaborate waited process places:
		if (arrivends != null)
			for (ExpressionNode arrivend : arrivends) {
				if (arrivend.expressionKind() == ExpressionKind.REGULAR_RANGE) {
					RegularRangeNode range = (RegularRangeNode) arrivend;

					results.add(createElaborateFor(range.getLow()));
					results.add(createElaborateFor(range.getHigh()));
				} else
					results.add(createElaborateFor(arrivend));
			}
		results.add(assumes);
		return results;
	}

	// TODO: add check for sequential and mpi
	List<BlockItemNode> transformAssignsClause(List<ExpressionNode> memLocSets)
			throws SyntaxException {
		List<BlockItemNode> results = new LinkedList<>();

		for (ExpressionNode memoryLocationSet : memLocSets)
			results.add(refreshMemoryLocationSetExpression(memoryLocationSet));
		return results;
	}

	/*
	 * *************************************************************************
	 * Pre-processing Methods :
	 **************************************************************************/
	private Pair<List<BlockItemNode>, ExpressionNode> allocation4Valids(
			ExpressionNode expression, TransformConfiguration config)
			throws SyntaxException {
		ASTNode astNode = expression;
		List<OperatorNode> validNodes = new LinkedList<>();
		List<MPIContractExpressionNode> mpiValidNodes = new LinkedList<>();
		List<BlockItemNode> results = new LinkedList<>();

		do {
			if (astNode instanceof OperatorNode) {
				OperatorNode opNode = (OperatorNode) astNode;

				if (opNode.getOperator() == Operator.VALID)
					validNodes.add(opNode);
			} else if (astNode instanceof MPIContractExpressionNode) {
				MPIContractExpressionNode mpiPrimitive = (MPIContractExpressionNode) astNode;

				if (mpiPrimitive
						.MPIContractExpressionKind() == MPIContractExpressionKind.MPI_VALID)
					mpiValidNodes.add(mpiPrimitive);
			}
		} while ((astNode = astNode.nextDFS()) != null);
		if (!config.isInMPIBlock() && !mpiValidNodes.isEmpty())
			throw new CIVLSyntaxException(
					"\\mpi_valid shall not be used in sequential contracts",
					mpiValidNodes.get(0).getSource());
		if (config.alloc4Valid()) {
			for (OperatorNode validNode : validNodes)
				results.addAll(allocate4ACSLValid(validNode));
			for (MPIContractExpressionNode mpiValidNode : mpiValidNodes)
				results.addAll(allocate4MPIValid(mpiValidNode));

			// TODO: do forgot checking "extent > 0"
			/* Replace valid/mpi_valid expressions with simple true literal */
			substituteAllValid2True(expression);
		}
		return new Pair<>(results, expression);
	}

	/**
	 * Replace all appearances of {@link ResultNode} with an identifier
	 * expression "$result" for the given expression;
	 * 
	 * @param expression
	 * @return
	 */
	private ExpressionNode result2intermediate(ExpressionNode expression,
			TransformConfiguration config) {
		ASTNode visitor = expression;
		LinkedList<ASTNode> resultNodes = new LinkedList<>();

		assert expression.parent() == null;
		while (visitor != null) {
			if (visitor instanceof ResultNode)
				resultNodes.add(visitor);
			visitor = visitor.nextDFS();
		}
		if (config.noResult() && !resultNodes.isEmpty())
			throw new CIVLSyntaxException(
					"No \\result is allowed to be in 'requires' clauses",
					expression.getSource());
		while (!resultNodes.isEmpty()) {
			ASTNode result = resultNodes.removeLast();
			ASTNode parent = result.parent();
			int childIdx = result.childIndex();
			ExpressionNode artificialVar = nodeFactory
					.newIdentifierExpressionNode(result.getSource(),
							nodeFactory.newIdentifierNode(result.getSource(),
									MPIContractUtilities.ACSL_RESULT_VAR));

			if (parent == null) {
				// The given predicate is an instance of result expression:
				assert resultNodes.isEmpty();
				return artificialVar;
			}
			result.remove();
			parent.setChild(childIdx, artificialVar);
		}
		return expression;
	}

	private Pair<List<BlockItemNode>, ExpressionNode> mpiExtent2intermediate(
			ExpressionNode predicate) {
		ASTNode visitor = predicate;
		LinkedList<MPIContractExpressionNode> mpiExtents = new LinkedList<>();
		List<BlockItemNode> intermediateVarDecls = new LinkedList<>();

		assert predicate.parent() == null;
		while (visitor != null) {
			if (visitor instanceof MPIContractExpressionNode) {
				MPIContractExpressionNode mpiExpr = (MPIContractExpressionNode) visitor;

				if (mpiExpr
						.MPIContractExpressionKind() == MPIContractExpressionKind.MPI_EXTENT)
					mpiExtents.add(mpiExpr);
			}
			visitor = visitor.nextDFS();
		}
		while (!mpiExtents.isEmpty()) {
			MPIContractExpressionNode mpiExpr = mpiExtents.remove();
			ASTNode parent = mpiExpr.parent();
			int childidx = mpiExpr.childIndex();
			ExpressionNode datatypeExpr = mpiExpr.getArgument(0);
			ExpressionNode mpiextentofCall = createMPIExtentofCall(
					mpiExpr.getArgument(0));
			TypeNode sizeTNode = nodeFactory.newTypedefNameNode(nodeFactory
					.newIdentifierNode(mpiExpr.getSource(), "size_t"), null);
			String intermediateVarName = null;
			String datatypeIdName = null;

			if (datatypeExpr instanceof IdentifierExpressionNode)
				datatypeIdName = ((IdentifierExpressionNode) datatypeExpr)
						.getIdentifier().name();
			else if (datatypeExpr instanceof EnumerationConstantNode)
				datatypeIdName = ((EnumerationConstantNode) datatypeExpr)
						.getName().name();
			if (datatypeIdName != null)
				intermediateVarName = datatype2counter.get(datatypeIdName);
			if (intermediateVarName == null) {
				VariableDeclarationNode intermediateVarDecl;

				intermediateVarName = MPIContractUtilities
						.nextExtentName(tmpExtentCounter++);
				datatype2counter.put(datatypeIdName, intermediateVarName);
				intermediateVarDecl = nodeFactory.newVariableDeclarationNode(
						mpiExpr.getSource(),
						nodeFactory.newIdentifierNode(mpiExpr.getSource(),
								intermediateVarName),
						sizeTNode, mpiextentofCall);
				intermediateVarDecls.add(intermediateVarDecl);
			}

			ExpressionNode intermediateVarExpr = nodeFactory
					.newIdentifierExpressionNode(mpiExpr.getSource(),
							nodeFactory.newIdentifierNode(mpiExpr.getSource(),
									intermediateVarName));
			if (parent == null) {
				assert mpiExpr == predicate;
				return new Pair<>(intermediateVarDecls, intermediateVarExpr);
			}
			mpiExpr.remove();
			parent.setChild(childidx, intermediateVarExpr);
		}
		return new Pair<>(intermediateVarDecls, predicate);
	}

	/**
	 * Replace all OLD expressions with VALUE_AT expressions.
	 * 
	 * @param predicate
	 *            The predicate may contain OLD expressions.
	 * @param preState
	 *            The pre collate state
	 * @param config
	 * @return The predicate after substitution.
	 */
	private ExpressionNode old2ValueAt(ExpressionNode predicate,
			ExpressionNode preState, TransformConfiguration config) {
		ASTNode visitor = predicate;
		LinkedList<ExpressionNode[]> oldExprs = new LinkedList<>();

		assert predicate.parent() == null;
		while (visitor != null) {
			if (visitor instanceof OperatorNode) {
				OperatorNode opNode = (OperatorNode) visitor;
				ExpressionNode rankConstant = nodeFactory
						.newIdentifierExpressionNode(opNode.getSource(),
								nodeFactory.newIdentifierNode(
										opNode.getSource(),
										MPIContractUtilities.MPI_COMM_RANK_CONST));

				if (opNode.getOperator() == Operator.OLD) {
					ExpressionNode[] valueAtArgs = {null, rankConstant,
							opNode.getArgument(0), opNode};
					oldExprs.add(valueAtArgs);
				}
			}
			visitor = visitor.nextDFS();
		}
		for (ExpressionNode[] valueAtArgs : oldExprs)
			predicate = replaceWithValueAt(valueAtArgs[0], valueAtArgs[1],
					valueAtArgs[2], valueAtArgs[3], predicate);
		return predicate;
	}

	/**
	 * Replace all OLD expressions with VALUE_AT expressions.
	 * 
	 * @param predicate
	 *            The predicate may contain OLD expressions.
	 * @param preState
	 *            The pre collate state
	 * @param config
	 * @return The predicate after substitution.
	 */
	private ExpressionNode on2ValueAt(ExpressionNode predicate,
			ExpressionNode preState, TransformConfiguration config) {
		ASTNode visitor = predicate;
		// a list of an array of 4 expression nodes, which represents state,
		// process, expression and the original remote on expression
		// respectively:
		LinkedList<ExpressionNode[]> onExprs = new LinkedList<>();

		assert predicate.parent() == null;
		while (visitor != null) {
			if (visitor instanceof RemoteOnExpressionNode) {
				RemoteOnExpressionNode onNode = (RemoteOnExpressionNode) visitor;
				ExpressionNode valueAtArgs[] = {preState,
						onNode.getProcessExpression(),
						onNode.getForeignExpressionNode(), onNode};

				onExprs.add(valueAtArgs);
			}
			visitor = visitor.nextDFS();
		}
		for (ExpressionNode valueAtArgs[] : onExprs)
			predicate = replaceWithValueAt(valueAtArgs[0], valueAtArgs[1],
					valueAtArgs[2], valueAtArgs[3], predicate);
		return predicate;
	}

	private ExpressionNode replaceWithValueAt(ExpressionNode state,
			ExpressionNode proc, ExpressionNode expr, ExpressionNode original,
			ExpressionNode root) {
		ASTNode parent = original.parent();
		int childIdx = original.childIndex();
		ExpressionNode valueAt;

		if (state == null)
			state = MPIContractUtilities
					.getStateNullExpression(original.getSource(), nodeFactory);
		state.remove();
		proc.remove();
		expr.remove();
		valueAt = nodeFactory.newValueAtNode(original.getSource(), state, proc,
				expr);
		if (parent != null) {
			original.remove();
			parent.setChild(childIdx, valueAt);
			return root;
		} else {
			assert root == original;
			return valueAt;
		}
	}
	/*
	 * *************************************************************************
	 * Methods creating new statements:
	 **************************************************************************/
	/**
	 * <p>
	 * <b>Summary: </b> Creates an assertion function call with an argument
	 * "predicate".
	 * </p>
	 * 
	 * @param predicate
	 *            The {@link ExpressionNode} which represents a predicate. It is
	 *            the only argument of an assertion call.
	 * @return A created assert call statement node;
	 */
	StatementNode createAssertion(ExpressionNode predicate) {
		ExpressionNode assertIdentifier = nodeFactory
				.newIdentifierExpressionNode(predicate.getSource(),
						nodeFactory.newIdentifierNode(predicate.getSource(),
								BaseWorker.ASSERT));
		FunctionCallNode assumeCall = nodeFactory.newFunctionCallNode(
				predicate.getSource(), assertIdentifier,
				Arrays.asList(predicate), null);
		return nodeFactory.newExpressionStatementNode(assumeCall);
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
	 * @return A created assumption call statement node;
	 */
	StatementNode createAssumption(ExpressionNode predicate) {
		ExpressionNode assumeIdentifier = identifierExpressionNode(
				predicate.getSource(), BaseWorker.ASSUME);
		FunctionCallNode assumeCall = nodeFactory.newFunctionCallNode(
				predicate.getSource(), assumeIdentifier,
				Arrays.asList(predicate), null);
		return nodeFactory.newExpressionStatementNode(assumeCall);
	}

	/**
	 * <p>
	 * Allocates for valid expressions.
	 * </p>
	 * 
	 * <p>
	 * Currently it only can deal with a fixed form:
	 * <code>\valid( ptr + integr-set)</code>, where
	 * <code>integr-set := regular_range (with default step)  
	 *                     | integer;
	 *                     
	 *       ptr must have type T* and T shall not be void;
	 * </code>
	 * </p>
	 * 
	 * @param valid
	 *            A valid expression
	 * @return A list of {@link BlockItemNode} express the allocation of the
	 *         valid expression.
	 * @throws SyntaxException
	 *             If the valid expression is not written in the canonical form.
	 */
	private List<BlockItemNode> allocate4ACSLValid(OperatorNode valid)
			throws SyntaxException {
		Source source = valid.getSource();
		ExpressionNode argument = valid.getArgument(0);
		ExpressionNode pointer, range = null;

		// Check if the argument of valid is in canonical form:
		if (argument instanceof OperatorNode) {
			OperatorNode opNode = (OperatorNode) argument;
			if (opNode.getOperator() != Operator.PLUS)
				throw new CIVLSyntaxException(
						"CIVL requires the argument of \\valid "
								+ "expression to be a canonical form:\n"
								+ "ptr (+ range)*\n"
								+ "range := integer-expression "
								+ "| integer-expression .. integer-expression",
						opNode.getSource());
			pointer = opNode.getArgument(0);
			range = opNode.getArgument(1);
			range = makeItRange(range);
		} else
			pointer = argument;

		assert pointer.getType().kind() == TypeKind.POINTER;
		PointerType ptrType = (PointerType) pointer.getType();
		ExpressionNode count;

		if (ptrType.referencedType().kind() == TypeKind.VOID)
			throw new CIVLSyntaxException(
					"Valid pointers asserted by \\valid expressions"
							+ " shall not have pointer-to-void type",
					pointer.getSource());

		if (range != null) {
			RegularRangeNode rangeNode = (RegularRangeNode) range;
			ExpressionNode high = rangeNode.getHigh();
			ExpressionNode low = rangeNode.getLow();
			Value constantVal = nodeFactory.getConstantValue(low);

			count = constantVal.isZero() == Answer.YES
					? high
					: nodeFactory.newOperatorNode(range.getSource(),
							Operator.MINUS, Arrays.asList(high, low));
		} else
			count = nodeFactory.newIntegerConstantNode(source, "1");

		Source ptrSource = pointer.getSource();
		TypeNode referedTypeNode;

		pointer = decast(pointer);
		referedTypeNode = BaseWorker.typeNode(ptrSource,
				ptrType.referencedType(), nodeFactory);

		// For \valid(ptr + x), there must equivalently be an array ptr[extent]
		// where extent >= x + 1:
		OperatorNode extent = nodeFactory.newOperatorNode(pointer.getSource(),
				Operator.PLUS, count.copy(), count = nodeFactory
						.newIntegerConstantNode(pointer.getSource(), "1"));

		return createAllocation(pointer, referedTypeNode, extent, ptrSource);
	}

	/**
	 * Allocates for \mpi_valid expressions.
	 * 
	 * @param condition
	 *            branch condition
	 * @param mpiValid
	 *            the \mpi_valid expression
	 * @param outputTriple
	 *            the output triple will be added with free statements
	 * @return
	 * @throws SyntaxException
	 */
	private List<BlockItemNode> allocate4MPIValid(
			MPIContractExpressionNode mpiValid) throws SyntaxException {
		Source source = mpiValid.getSource();
		ExpressionNode buf = mpiValid.getArgument(0);
		ExpressionNode count = mpiValid.getArgument(1);
		ExpressionNode datatype = mpiValid.getArgument(2);
		TypeNode typeNode;

		if (datatype instanceof EnumerationConstantNode) {
			EnumerationConstantNode mpiDatatypeConstant = (EnumerationConstantNode) datatype;
			String name = mpiDatatypeConstant.getName().name();
			String typedefname = "_" + name + "_t"; // quick translation

			typeNode = nodeFactory.newTypedefNameNode(nodeFactory
					.newIdentifierNode(datatype.getSource(), typedefname),
					null);
		} else {
			typeNode = nodeFactory.newBasicTypeNode(datatype.getSource(),
					BasicTypeKind.CHAR);

			// optimize, reduce the number of intermediate variables introduced
			// by side-effect remover:
			String intermediateVarName = null, datatypeIdentifierName = null;
			ExpressionNode extentofDatatype;

			if (datatype instanceof IdentifierExpressionNode)
				datatypeIdentifierName = ((IdentifierExpressionNode) datatype)
						.getIdentifier().name();
			else if (datatype instanceof EnumerationConstantNode)
				datatypeIdentifierName = ((EnumerationConstantNode) datatype)
						.getName().name();
			if (datatypeIdentifierName != null)
				intermediateVarName = datatype2counter
						.get(datatypeIdentifierName);
			if (intermediateVarName != null)
				extentofDatatype = nodeFactory.newIdentifierExpressionNode(
						datatype.getSource(), nodeFactory.newIdentifierNode(
								datatype.getSource(), intermediateVarName));
			else
				extentofDatatype = createMPIExtentofCall(datatype);
			// char data[count * extentof(datatype)];
			count = nodeFactory.newOperatorNode(source, Operator.TIMES,
					Arrays.asList(count.copy(), extentofDatatype));
		}
		return createAllocation(buf, typeNode, count, source);
	}

	/**
	 * @return a function call expression:
	 *         <code>$collate_get_state(colStateRef) </code>
	 */
	private ExpressionNode createCollateGetStateCall(ExpressionNode colStateRef,
			Source source) {
		return nodeFactory.newFunctionCallNode(source,
				identifierExpressionNode(source,
						MPIContractUtilities.COLLATE_GET_STATE_CALL),
				Arrays.asList(colStateRef.copy()), null);
	}

	/**
	 * @param a
	 *            function call expression: <code>$elaborate(expr)</code>
	 * @return
	 */
	private StatementNode createElaborateFor(ExpressionNode expression) {
		IdentifierExpressionNode funcIdent = nodeFactory
				.newIdentifierExpressionNode(expression.getSource(),
						nodeFactory.newIdentifierNode(expression.getSource(),
								BaseWorker.ELABORATE));
		ExpressionNode elaborateCall = nodeFactory.newFunctionCallNode(
				expression.getSource(), funcIdent,
				Arrays.asList(expression.copy()), null);

		return nodeFactory.newExpressionStatementNode(elaborateCall);
	}

	/**
	 * Create statements simulating allocation, i.e. declare an new artificial
	 * array variable then assign the reference to the given pointer.
	 * 
	 * @param pointer
	 *            A pointer expression p
	 * @param elementType
	 *            element type t
	 * @param numElements
	 *            number of elements n
	 * @param source
	 * @return A list of artifical {@link BlockItemNode}s
	 * @throws SyntaxException
	 */
	private List<BlockItemNode> createAllocation(ExpressionNode pointer,
			TypeNode elementType, ExpressionNode numElements, Source source)
			throws SyntaxException {
		List<BlockItemNode> artificials = new LinkedList<>();
		ExpressionNode extentGTzero = nodeFactory.newOperatorNode(source,
				Operator.LT, nodeFactory.newIntegerConstantNode(source, "0"),
				numElements.copy());
		TypeNode arrayType = nodeFactory.newArrayTypeNode(source,
				elementType.copy(), numElements.copy());
		String allocationName = MPIContractUtilities
				.nextAllocationName(tmpHeapCounter++);
		IdentifierNode allocationIdentifierNode;

		allocationIdentifierNode = nodeFactory
				.newIdentifierNode(pointer.getSource(), allocationName);

		VariableDeclarationNode artificialVariable = nodeFactory
				.newVariableDeclarationNode(source, allocationIdentifierNode,
						arrayType);
		// assign allocated object to pointer;
		ExpressionNode assign = nodeFactory.newOperatorNode(source,
				Operator.ASSIGN,
				Arrays.asList(pointer.copy(),
						nodeFactory.newIdentifierExpressionNode(source,
								allocationIdentifierNode.copy())));

		sideEffectConditions.add(extentGTzero);
		artificials.add(createAssumption(extentGTzero));
		artificials.add(artificialVariable);
		artificials.add(nodeFactory.newExpressionStatementNode(assign));
		return artificials;
	}

	/**
	 * 
	 * <p>
	 * <b>Summary: </b> Creates an $havoc_mem function call:
	 * </p>
	 * 
	 * @param var
	 * @return
	 */
	private ExpressionNode createHavocCall(ExpressionNode addr) {
		Source source = addr.getSource();
		ExpressionNode callIdentifier = identifierExpressionNode(source,
				MPIContractUtilities.HAVOC);

		addr = nodeFactory.newOperatorNode(source, Operator.ADDRESSOF,
				Arrays.asList(addr));

		FunctionCallNode call = nodeFactory.newFunctionCallNode(source,
				callIdentifier, Arrays.asList(addr), null);

		return call;
	}

	private StatementNode withStatementWrapper(StatementNode body,
			ExpressionNode collateState, List<ExpressionNode> dependents,
			TransformConfiguration config) {
		StatementNode withStmt = nodeFactory.newWithNode(body.getSource(),
				collateState.copy(), body.copy());
		if (config.getWith())
			return withStmt;
		boolean run = config.getRunWithComplete() || config.getRunWithArrived();
		boolean complete = config.getWithComplete()
				|| config.getRunWithComplete() || dependents.isEmpty();

		if (complete) {
			ExpressionNode functionIdentifier = nodeFactory
					.newIdentifierExpressionNode(body.getSource(),
							nodeFactory.newIdentifierNode(body.getSource(),
									MPIContractUtilities.COLLATE_COMPLETE));
			ExpressionNode collateComplete = nodeFactory.newFunctionCallNode(
					collateState.getSource(), functionIdentifier,
					Arrays.asList(collateState.copy()), null);
			StatementNode withCompleteStmt = nodeFactory.newWhenNode(
					collateComplete.getSource(), collateComplete, withStmt);

			if (run)
				return nodeFactory.newRunNode(withCompleteStmt.getSource(),
						withCompleteStmt);
			else
				return withCompleteStmt;
		}
		if (config.getRunWithArrived()) {
			ExpressionNode functionIdentifier = nodeFactory
					.newIdentifierExpressionNode(body.getSource(),
							nodeFactory.newIdentifierNode(body.getSource(),
									MPIContractUtilities.COLLATE_ARRIVED));
			ExpressionNode allArrived = null;

			for (ExpressionNode dependent : dependents) {
				ExpressionNode arrived = nodeFactory.newFunctionCallNode(
						collateState.getSource(), functionIdentifier.copy(),
						Arrays.asList(collateState.copy(),
								makeItRange(dependent)),
						null);
				Source arrivedSource = arrived.getSource();

				allArrived = allArrived == null
						? arrived
						: nodeFactory.newOperatorNode(arrivedSource,
								Operator.LAND,
								Arrays.asList(allArrived, arrived));

			}
			return nodeFactory.newRunNode(withStmt.getSource(), nodeFactory
					.newWhenNode(allArrived.getSource(), allArrived, withStmt));
		}
		return body;
	}

	/*
	 * *************************************************************************
	 * Miscellaneous helper methods:
	 **************************************************************************/
	private List<BlockItemNode> mpiConstantsInitialization(
			ExpressionNode mpiComm) {
		List<BlockItemNode> results = new LinkedList<>();
		ExpressionNode rank = nodeFactory.newIdentifierExpressionNode(
				mpiComm.getSource(),
				nodeFactory.newIdentifierNode(mpiComm.getSource(),
						MPIContractUtilities.MPI_COMM_RANK_CONST));
		ExpressionNode size = nodeFactory.newIdentifierExpressionNode(
				mpiComm.getSource(),
				nodeFactory.newIdentifierNode(mpiComm.getSource(),
						MPIContractUtilities.MPI_COMM_SIZE_CONST));

		results.add(createMPICommRankCall(mpiComm.copy(), rank));
		results.add(createMPICommSizeCall(mpiComm.copy(), size));
		return results;
	}

	private StatementNode createMPICommRankCall(ExpressionNode mpiComm,
			ExpressionNode rankVar) {
		ExpressionNode callIdentifier = nodeFactory.newIdentifierExpressionNode(
				rankVar.getSource(),
				nodeFactory.newIdentifierNode(rankVar.getSource(),
						MPIContractUtilities.MPI_COMM_RANK_CALL));
		ExpressionNode addressOfRank = nodeFactory.newOperatorNode(
				rankVar.getSource(), Operator.ADDRESSOF, rankVar.copy());
		FunctionCallNode call = nodeFactory.newFunctionCallNode(
				rankVar.getSource(), callIdentifier,
				Arrays.asList(mpiComm.copy(), addressOfRank), null);
		return nodeFactory.newExpressionStatementNode(call);
	}

	private StatementNode createMPICommSizeCall(ExpressionNode mpiComm,
			ExpressionNode sizeVar) {
		ExpressionNode callIdentifier = nodeFactory.newIdentifierExpressionNode(
				sizeVar.getSource(),
				nodeFactory.newIdentifierNode(sizeVar.getSource(),
						MPIContractUtilities.MPI_COMM_SIZE_CALL));
		ExpressionNode addressOfSize = nodeFactory.newOperatorNode(
				sizeVar.getSource(), Operator.ADDRESSOF, sizeVar.copy());
		FunctionCallNode call = nodeFactory.newFunctionCallNode(
				sizeVar.getSource(), callIdentifier,
				Arrays.asList(mpiComm.copy(), addressOfSize), null);
		return nodeFactory.newExpressionStatementNode(call);
	}

	private ExpressionNode createMPIExtentofCall(ExpressionNode datatype) {
		ExpressionNode callIdentifier = nodeFactory.newIdentifierExpressionNode(
				datatype.getSource(),
				nodeFactory.newIdentifierNode(datatype.getSource(),
						MPIContractUtilities.MPI_EXTENT_OF));

		return nodeFactory.newFunctionCallNode(datatype.getSource(),
				callIdentifier, Arrays.asList(datatype.copy()), null);
	}

	// TODO: doc
	private ExpressionNode mpiRegion2assign(
			MPIContractExpressionNode mpiRegion) {
		assert mpiRegion
				.MPIContractExpressionKind() == MPIContractExpressionKind.MPI_REGION;
		Source source = mpiRegion.getSource();
		ExpressionNode ptr = mpiRegion.getArgument(0);
		ExpressionNode count = mpiRegion.getArgument(1);
		ExpressionNode extent = mpiRegion.getArgument(2);
		ExpressionNode call = nodeFactory.newFunctionCallNode(source,
				identifierExpressionNode(source,
						MPIContractUtilities.MPI_ASSIGNS),
				Arrays.asList(ptr.copy(), count.copy(), extent.copy()), null);

		return call;
	}

	private ExpressionNode createMPIBarrier(ExpressionNode mpiComm) {
		ExpressionNode functionIdentifierExpression = nodeFactory
				.newIdentifierExpressionNode(mpiComm.getSource(),
						nodeFactory.newIdentifierNode(mpiComm.getSource(),
								MPIContractUtilities.MPI_BARRIER_CALL));

		return nodeFactory.newFunctionCallNode(mpiComm.getSource(),
				functionIdentifierExpression, Arrays.asList(mpiComm.copy()),
				null);
	}

	private ExpressionNode createMPICommEmptyCall(ExpressionNode mpiComm,
			MPICommunicatorMode mode) {
		ExpressionNode functionIdentifierExpression = nodeFactory
				.newIdentifierExpressionNode(mpiComm.getSource(),
						nodeFactory.newIdentifierNode(mpiComm.getSource(),
								MPIContractUtilities.MPI_CHECK_EMPTY_COMM));
		String mpiCommModeName = mode == MPICommunicatorMode.P2P
				? MPIContractUtilities.MPI_COMM_P2P_MODE
				: MPIContractUtilities.MPI_COMM_COL_MODE;
		ExpressionNode modeEnum = nodeFactory.newEnumerationConstantNode(
				nodeFactory.newIdentifierNode(mpiComm.getSource(),
						mpiCommModeName));

		return nodeFactory.newFunctionCallNode(mpiComm.getSource(),
				functionIdentifierExpression,
				Arrays.asList(mpiComm.copy(), modeEnum), null);
	}

	private VariableDeclarationNode createCollateStateInitializer(
			String collateStateName, ExpressionNode mpiComm) {
		Source source = mpiComm.getSource();
		InitializerNode initializer = createMPISnapshotCall(mpiComm.copy());
		TypeNode collateStateTypeName = nodeFactory
				.newTypedefNameNode(nodeFactory.newIdentifierNode(source,
						MPIContractUtilities.COLLATE_STATE_TYPE), null);
		IdentifierNode varIdent = nodeFactory.newIdentifierNode(source,
				collateStateName);

		return nodeFactory.newVariableDeclarationNode(source, varIdent,
				collateStateTypeName, initializer);
	}

	private ExpressionNode createMPISnapshotCall(ExpressionNode mpiComm) {
		Source source = mpiComm.getSource();
		ExpressionNode callIdentifier = nodeFactory.newIdentifierExpressionNode(
				source, nodeFactory.newIdentifierNode(source,
						MPIContractUtilities.MPI_SNAPSHOT));
		ExpressionNode hereNode = nodeFactory.newHereNode(source);
		FunctionCallNode call = nodeFactory.newFunctionCallNode(source,
				callIdentifier, Arrays.asList(mpiComm.copy(), hereNode), null);

		return call;
	}

	/*
	 * *************************************************************************
	 * Methods process ASSIGNS clauses
	 **************************************************************************/
	/**
	 * Process ACSL <b>assigns memory-location-set-list</b> clauses:
	 * 
	 * For callee functions, memory locations specified by <b>assigns</b> must
	 * be refreshed, i.e. assigned with fresh new symbolic constants.
	 */
	/**
	 * Assign fresh new symbolic constants to a memory locaton set expression.
	 * <p>
	 * A memory-location-set is
	 * <ol>
	 * <li>a set of l-values (including singleton set). According to ACSL
	 * reference v1.10 2.3.4, an expression representing a set of l-values can
	 * be formed with following rules (which are supported by CIVL):
	 * <ul>
	 * <li>set-&gtid := {x-&gtid | x in set}</li>
	 * <li>set.id := {x.id | x in set}</li>
	 * <li>*set := {*x | x in set}</li>
	 * <li>s1[s2] := { x1[x2] | x1 in s1, x2 in s2 }</li>
	 * <li><b>Base case:</b> t1 ... t2 := a set of integers in between [t1, t2]
	 * </li> Notice that there are two set expressions supported by CIVL but
	 * will never be able to express memory location set: &set and set1 + set2
	 * </ul>
	 * </li>
	 * <li>an MPI_REGION expression</li>
	 * </ol>
	 * </p>
	 * 
	 * <p>
	 * <b>For the expression e that represents a set of l-values, </b> this
	 * method returns a statement s for assigning fresh new symbolic constants
	 * to e: <br>
	 * <br>
	 * <code>
	 * s := $for(int i0 : r0)
	 *       $for(int i1 : r1)
	 *        ...
	 *         $for(int in : rn)
	 *           $havoc(addressof(e[i0/r0, i1/r1,...,in/rn]));     
	 * </code> where {r0,...rn} is the set R of base cases which consistitute e.
	 * </p>
	 * 
	 * <p>
	 * <b>For an MPI_REGION expression,</b> this method creates a call to the
	 * function<code>$mpi_assigns</code> which is defined in civl-mpi.cvl
	 * </p>
	 * 
	 * @param expression
	 *            An expression represents a memory location set
	 * @return A {@link BlockItemNode} which consists of statements that will
	 *         assign fresh new symbolic constants to the given expression
	 * @throws SyntaxException
	 *             When the given expression is not a valid memory location set
	 *             expression.
	 */
	private BlockItemNode refreshMemoryLocationSetExpression(
			ExpressionNode expression) throws SyntaxException {
		// if expression is an MPI_REGION expression:
		if (expression
				.expressionKind() == ExpressionKind.MPI_CONTRACT_EXPRESSION) {
			MPIContractExpressionNode mpiExpr = (MPIContractExpressionNode) expression;

			assert mpiExpr
					.MPIContractExpressionKind() == MPIContractExpressionKind.MPI_REGION;
			return nodeFactory
					.newExpressionStatementNode(mpiRegion2assign(mpiExpr));
		} else {
			Map<String, RegularRangeNode> baseCases = new HashMap<>();
			ExpressionNode havocee = processLvalueSetExpression(expression,
					baseCases);
			ExpressionNode havocCall = createHavocCall(havocee);
			StatementNode body = nodeFactory
					.newExpressionStatementNode(havocCall);
			TypeNode intTypeNode = nodeFactory.newBasicTypeNode(
					expression.getSource(), BasicTypeKind.INT);

			for (Entry<String, RegularRangeNode> entry : baseCases.entrySet()) {
				String loopIdentName = entry.getKey();
				RegularRangeNode range = entry.getValue();
				Source source = range.getSource();
				VariableDeclarationNode looIdentDecl = nodeFactory
						.newVariableDeclarationNode(source, nodeFactory
								.newIdentifierNode(source, loopIdentName),
								intTypeNode);
				DeclarationListNode declList = nodeFactory
						.newForLoopInitializerNode(source,
								Arrays.asList(looIdentDecl));

				body = nodeFactory.newCivlForNode(source, false, declList,
						range, body, null);
			}
			return body;
		}
	}

	/**
	 * <p>
	 * Given an expression e which represents an l-value set, this method will
	 * return <code>e[i0/r0, i1/r1,...,in/rn]</code> where {r0, r1, ...,rn} is
	 * the set of base cases (for base case, see
	 * {@link #refreshMemoryLocationSetExpression(ExpressionNode)}) constitute
	 * e, {i0, i1, ..., in} is a set of integer type identifiers.
	 * 
	 * </p>
	 * 
	 * @param lvalue
	 *            The given lvalue set expression
	 * @param baseCases
	 *            A map collection which will be added with a set of key-value
	 *            pairs (i, r) where i in {i0, i1, ..., in} and r is the
	 *            corresponding element in {r0, r1, ..., rn}
	 * @return
	 */
	private ExpressionNode processLvalueSetExpression(ExpressionNode lvalue,
			Map<String, RegularRangeNode> baseCases) {
		ExpressionNode copy = lvalue.copy();
		ASTNode node = copy;
		List<RegularRangeNode> ranges = new LinkedList<>();

		while (node != null) {
			if (node.nodeKind() == NodeKind.EXPRESSION
					&& ((ExpressionNode) node)
							.expressionKind() == ExpressionKind.REGULAR_RANGE) {
				ranges.add((RegularRangeNode) node);
			}
			node = node.nextDFS();
		}
		for (RegularRangeNode range : ranges) {
			String identifierName = MPIContractUtilities
					.nextAssignName(tmpAssignCounter++);
			ExpressionNode identifierExpression = identifierExpressionNode(
					range.getSource(), identifierName);
			ASTNode parent = range.parent();
			int childIdx = range.childIndex();

			range.remove();
			parent.setChild(childIdx, identifierExpression);
			baseCases.put(identifierName, range);
		}
		return copy;
	}

	/**
	 * @param rangeOrInteger
	 *            Either an integer type expression or a regular range
	 *            expression.
	 * @return A regular range whose low and high are both equal to the given
	 *         expression 'rangeOrInteger' iff 'rangeOrInteger' is not a regular
	 *         range expression. Otherwise return 'rangeOrInteger' directly.
	 */
	private ExpressionNode makeItRange(ExpressionNode rangeOrInteger) {
		if (rangeOrInteger.getType().kind() == TypeKind.RANGE)
			return rangeOrInteger.copy();
		assert rangeOrInteger.getType().kind() == TypeKind.BASIC;
		return nodeFactory.newRegularRangeNode(rangeOrInteger.getSource(),
				rangeOrInteger.copy(), rangeOrInteger.copy());
	}

	/**
	 * If the given expression is a cast-expression: <code>(T) expr</code>,
	 * return an expression representing <code>expr</code>, otherwise no-op.
	 * 
	 * @param expression
	 *            An instance of {@link ExpressionNode}
	 * @return An expression who is the argument of a cast expression iff the
	 *         input is a cast expression, otherwise returns input itself.(i.e.
	 *         no-op).
	 */
	private ExpressionNode decast(ExpressionNode expression) {
		if (expression.expressionKind() == ExpressionKind.CAST) {
			CastNode castNode = (CastNode) expression;

			return castNode.getArgument();
		}
		return expression;
	}

	private ExpressionNode substituteAllValid2True(ExpressionNode predicate) {
		ASTNode visitor = predicate;
		List<ASTNode> valids = new LinkedList<>();

		while (visitor != null) {
			if (visitor instanceof OperatorNode) {
				OperatorNode opNode = (OperatorNode) visitor;

				if (opNode.getOperator() == Operator.VALID)
					valids.add(opNode);
			}
			if (visitor instanceof MPIContractExpressionNode) {
				MPIContractExpressionNode mpiPrimitiveNode = (MPIContractExpressionNode) visitor;

				if (mpiPrimitiveNode
						.MPIContractExpressionKind() == MPIContractExpressionKind.MPI_VALID)
					valids.add(mpiPrimitiveNode);
			}
			visitor = visitor.nextDFS();
		}
		for (ASTNode valid : valids) {
			ASTNode parent;
			int childIdx;
			ExpressionNode trueLiteral = nodeFactory
					.newBooleanConstantNode(valid.getSource(), true);

			parent = valid.parent();
			childIdx = valid.childIndex();
			if (parent != null)
				parent.setChild(childIdx, trueLiteral);
			else {
				assert predicate == valid;
				return trueLiteral;
			}
		}
		return predicate;
	}

	private IdentifierExpressionNode identifierExpressionNode(Source source,
			String name) {
		return nodeFactory.newIdentifierExpressionNode(source,
				nodeFactory.newIdentifierNode(source, name));
	}
}
