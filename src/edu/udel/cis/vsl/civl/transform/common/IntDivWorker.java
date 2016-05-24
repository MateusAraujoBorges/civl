package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.OrdinaryEntity;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonContractNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonQuantifiedExpressionNode;
import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.front.IF.CivlcTokenConstant;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.transform.IF.IntDivisionTransformer;
import edu.udel.cis.vsl.civl.util.IF.CommonConstants;

/**
 * <p>
 * IntDivWorker is used by {@link IntDivisionTransformer}.
 * </p>
 * 
 * <p>
 * IntDivisionTransformer transforms all the integer division ('/') and integer
 * modulo ('%') in the program with $int_div(int, int) and $int_mod(int, int)
 * functions respectively.
 * </p>
 * 
 * @author yanyihao
 *
 */
public class IntDivWorker extends BaseWorker {

	/**
	 * division (\) and modulo (%) with quantified expression will not be
	 * influenced by this transformer.
	 */
	private boolean quantified = false;

	/* *******************static constants************************ */
	// TODO add java doc for every constant field
	private static final String INT_DIV = "$int_div";
	private static final String INT_MOD = "$int_mod";
	private static final String INT_DIV_SOURCE_FILE = "int_div.cvl";
	private static final String INT_DIV_NO_CHECKING = "int_div_no_checking.cvl";
	private static final String NO_CHECKING_DIVISION_BY_ZERO = "-checkDivisionByZero=false";

	public IntDivWorker(ASTFactory astFactory) {
		super(IntDivisionTransformer.LONG_NAME, astFactory);
		this.identifierPrefix = "_int_div_";
	}

	@Override
	public AST transform(AST unit) throws SyntaxException {
		SequenceNode<BlockItemNode> root = unit.getRootNode();
		AST newAst;

		OrdinaryEntity divEntity = unit.getInternalOrExternalEntity(INT_DIV);
		OrdinaryEntity modEntity = unit.getInternalOrExternalEntity(INT_MOD);
		if (divEntity != null || modEntity != null) {
			return unit;
		}
		unit.release();
		linkIntDivLibrary(root);
		processDivisionAndModulo(root);
		this.completeSources(root);
		newAst = astFactory.newAST(root, unit.getSourceFiles(), unit.isWholeProgram());
		return newAst;
	}

	/**
	 * <p>
	 * Go through the AST from the root node, replace {@link OperatorNode}s
	 * whose {@link Operator}s are {@link Operator#DIV} or {@link Operator#MOD}
	 * with functions $int_div or $int_mod defined in
	 * {@link #INT_DIV_SOURCE_FILE} respectively.
	 * </p>
	 * 
	 * <p>
	 * This only happens for integer division and integer modulo
	 * </p>
	 * 
	 * @param node
	 *            the node to be transformed
	 */
	private void processDivisionAndModulo(ASTNode node) {
		if (node instanceof FunctionDeclarationNode) {
			// the integer division ('/') and integer modulo ('%') in $int_div
			// and $int_mod functions should not be replaced.
			FunctionDeclarationNode funcDeclNode = (FunctionDeclarationNode) node;
			String name = funcDeclNode.getName();

			if (name.equals(INT_DIV) || name.equals(INT_MOD))
				return;
		}
		if (node instanceof OperatorNode && (((OperatorNode) node).getOperator() == Operator.DIV
				|| ((OperatorNode) node).getOperator() == Operator.MOD) && quantified == false) {
			OperatorNode opn = (OperatorNode) node;

			if (opn.getNumberOfArguments() != 2) {
				throw new CIVLSyntaxException("div or mod operator can only have two operands");
			}

			ASTNode parent = opn.parent();
			int childIndex = opn.childIndex();
			Operator op = opn.getOperator();
			ExpressionNode operand1 = opn.getArgument(0);
			ExpressionNode operand2 = opn.getArgument(1);

			processDivisionAndModulo(operand1);
			processDivisionAndModulo(operand2);
			operand1 = opn.getArgument(0);
			operand2 = opn.getArgument(1);
			if (operand1.getConvertedType() instanceof IntegerType
					&& operand2.getConvertedType() instanceof IntegerType) {
				// construct a new functionCallNode.
				String funcName = op == Operator.DIV ? INT_DIV : INT_MOD;
				String method = op == Operator.DIV ? INT_DIV + "()" : INT_MOD + "()";
				Source source = this.newSource(method, CivlcTokenConstant.CALL);
				List<ExpressionNode> args = new ArrayList<ExpressionNode>();

				operand1.remove();
				operand2.remove();
				args.add(operand1);
				args.add(operand2);

				FunctionCallNode funcCallNode = functionCall(source, funcName, args);

				funcCallNode.setInitialType(opn.getConvertedType());
				parent.setChild(childIndex, funcCallNode);
			}
		} else {
			for (ASTNode child : node.children()) {
				if (child != null) {
					if ((child instanceof CommonQuantifiedExpressionNode || child instanceof CommonContractNode)
							&& quantified == false) {
						quantified = true;
						processDivisionAndModulo(child);
						quantified = false;
					} else
						processDivisionAndModulo(child);
				}
			}
		}
	}

	/**
	 * This method will construct an AST from {@link #INT_DIV_SOURCE_FILE} ,
	 * then retrieve the declaration of function '$assert' and the definitions
	 * of functions '$int_div' and '$int_mod', then insert them to the top of
	 * the ast
	 * 
	 * @param ast
	 *            the root node of the AST into which the declarations are
	 *            inserted.
	 * @throws SyntaxException
	 *             when there are syntax error in {@link #INT_DIV_SOURCE_FILE}
	 */
	private void linkIntDivLibrary(SequenceNode<BlockItemNode> ast) throws SyntaxException {
		AST intDivLib;

		if (checkDivisionByZero()) {
			intDivLib = this.parseSystemLibrary(INT_DIV_SOURCE_FILE);
		} else {
			intDivLib = this.parseSystemLibrary(INT_DIV_NO_CHECKING);
		}

		SequenceNode<BlockItemNode> root = intDivLib.getRootNode();
		List<BlockItemNode> funcDefinitions = new ArrayList<>();

		intDivLib.release();
		for (BlockItemNode child : root) {
			child.remove();
			funcDefinitions.add(child);
		}
		ast.insertChildren(0, funcDefinitions);
	}

	private boolean checkDivisionByZero() {
		String currentCmd = CommonConstants.current_command_line;

		if (currentCmd != null) {
			if (currentCmd.trim().contains(NO_CHECKING_DIVISION_BY_ZERO))
				return false;
			else
				return true;
		} else
			return true;
	}
}
