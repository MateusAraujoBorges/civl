package edu.udel.cis.vsl.civl.transform.common;

import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.util.IF.Pair;

class ContractClauseTransformer {
	/**
	 * A reference to an instance of {@link BaseWorker}
	 */
	private BaseWorker baseWorker;

	/**
	 * A reference to an instance of {@link ASTFactory}
	 */
	private ASTFactory astFactory;

	/**
	 * A reference to an instance of {@link NodeFactory}
	 */
	private NodeFactory nodeFactory;

	/**
	 * A TransformTriple is an object consists of sets statements and an
	 * expression. An instance of a TransformTriple is a returned result of a
	 * contract transformation process. In common, a contract transformation
	 * process may return
	 * <li>some statements that should be inserted before the associated
	 * function being called (no-op in deduction circumstances);</li>
	 * <li>some statements that should be inserted at where associating to the
	 * contract clause (requires, ensures or assigns)</li>
	 * <li>an modified predicate expression which is specified by some contract
	 * clauses.
	 * 
	 * @author ziqingluo
	 *
	 */
	private class TransformTriple {
		List<BlockItemNode> preFuncStmts;
		List<BlockItemNode> currFuncStmts;
		ExpressionNode transformedExpression;

		TransformTriple() {
			this.preFuncStmts = new LinkedList<>();
			this.currFuncStmts = new LinkedList<>();
			transformedExpression = null;
		}
	}

	ContractClauseTransformer(BaseWorker baseWorker, ASTFactory astFactory) {
		this.baseWorker = baseWorker;
		this.astFactory = astFactory;
		this.nodeFactory = astFactory.getNodeFactory();
	}

	Pair<List<BlockItemNode>, ExpressionNode> preprocessClause(
			ExpressionNode condition, ExpressionNode predicate,
			ExpressionNode pre_state) throws SyntaxException {
		return null;
	}

	/**
	 * Transform a predicate specified by a contract clause into checking
	 * conditions C. Each c in C is a condition that should be checked and
	 * proved to true. The returned set of {@link BlockItemNode} can be any kind
	 * of nodes serving such a checking purpose, they can be declarations of
	 * temporary variables, assertion statements or functions call. etc.
	 * 
	 * @param condition
	 *            The condition or assumption under where the predicate should
	 *            hold.
	 * @param predicate
	 *            The predicate expression
	 * @return
	 * @throws SyntaxException
	 */
	Pair<List<BlockItemNode>, List<BlockItemNode>> transformClause2Checking(
			ExpressionNode condition, ExpressionNode predicate)
			throws SyntaxException {

		// conditional transformation:
		// wrap as assertions:
		// add extra condition:
		return null;
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
	 * @return
	 */
	Pair<List<BlockItemNode>, List<BlockItemNode>> transformClause2Assumption(
			ExpressionNode condition, ExpressionNode predicate) {
		return null;

	}

	/**
	 * Transform a set of l-value expressions E into a set of "assigns"
	 * statements A. Each a in A will assign a new unique symbolic constant to a
	 * e in E. The returned set of {@link BlockItemNode} can be any kind of
	 * nodes serving such a "assigns" purpose, they can be declarations of
	 * temporary variables, assignments or CIVL-C system function calls, etc.
	 * 
	 * @param condition
	 *            The condition or assumption under where the predicate should
	 *            hold.
	 * @param l_value_exprs
	 *            A set of l-value expressions which represent a set of memory
	 *            locations.
	 * @return
	 */
	Pair<List<BlockItemNode>, List<BlockItemNode>> transformAssignsClause(
			ExpressionNode condition, List<ExpressionNode> l_value_exprs) {
		return null;

	}

	/**
	 * Wraps a set of {@link BlockItemNode}s S with a $with directive w. That
	 * means that the execution of S is guarded by a condition specified by w
	 * and will start from a state specified by w.
	 * 
	 * @param collateState
	 *            The state associates to a $with directive.
	 * @param syncCondition
	 *            The condition that guards of execution of the body wrapped by
	 *            a $with directive
	 * @param body
	 *            The body S that will be wrapped by the $with directive
	 * @return
	 */
	List<BlockItemNode> continuationWrapper(ExpressionNode collateState,
			ExpressionNode syncCondition, List<BlockItemNode> body) {
		return null;

	}

	/*
	 * *************************************************************************
	 * Methods manipulating predicates:
	 **************************************************************************/

	/**
	 * Find out all <code>\valid</code> expression set V in the given expression
	 * e. Returns a pair of e':=e[v/true] where v in V and a list of predicates
	 * A, each a in A represents a v in V.
	 * 
	 * @param returnPredicateSet
	 *            The {@link Pair#right} will be a set of assertions for
	 *            checking those carved out valid expression if and only if this
	 *            parameter is true.
	 * @param expression
	 *            The expression may contains valid expression
	 * @return A {@link Pair}, whose left is the new expression e':=e[v/true]
	 *         where v in V; right is a set of predicates A if
	 *         returnPredicateSet is set true.
	 * @throws SyntaxException
	 */
	private Pair<ExpressionNode, List<ExpressionNode>> carveOutValidExpressions(
			ExpressionNode expression) throws SyntaxException {
		return null;
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
	 * @param source
	 *            The {@link Source} of the created function call statement
	 *            node;
	 * @return A created assert call statement node;
	 */
	private StatementNode createAssertion(ExpressionNode predicate) {
		return null;
	}

	/**
	 * Find out all <code>\old</code> expressions in the given expression and
	 * replace them with $value_at expressions:
	 * 
	 * @param expression
	 * @return
	 */
	private ExpressionNode replaceOldExpressionNodes4collective(
			ExpressionNode expression, ExpressionNode pre_state_state) {
		return null;
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
	private Pair<List<BlockItemNode>, ExpressionNode> replaceOldExpressionNodes4Local(
			ExpressionNode expression) throws SyntaxException {
		return null;
	}
}
