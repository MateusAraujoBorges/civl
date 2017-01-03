package edu.udel.cis.vsl.civl.transform.common;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonContractNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonQuantifiedExpressionNode;
import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.SignedIntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardUnsignedIntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardUnsignedIntegerType.UnsignedIntKind;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.UnsignedIntegerType;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory.Answer;
import edu.udel.cis.vsl.abc.front.IF.CivlcTokenConstant;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.transform.IF.IntOperationTransformer;

/**
 * <p>
 * IntDivWorker is used by {@link IntOperationTransformer}.
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
public class IntOperationWorker extends BaseWorker {

	/* *******************static constants************************ */
	// TODO add java doc for every constant field
	private static final String INT_DIV = "$int_div";
	private static final String INT_MOD = "$int_mod";
	private static final String ASSERT = "$assert";
	private static final String INT_DIV_SOURCE_FILE = "int_div.cvl";
	private static final String UNSIGNED_ADD = "$unsigned_add";
	private static final String UNSIGNED_SUBSTRACT = "$unsigned_subtract";
	private static final String UNSIGNED_MULTIPLY = "$unsigned_multiply";
	private static final String SIGNED_TO_UNSIGNED = "$signed_to_unsigned";
	private static final String UNSIGNED_NEG = "$unsigned_neg";
	private static final String UNSIGNED_ARITH_SOURCE_FILE = "unsigned_arith.cvl";
	// private static final String INT_DIV_NO_CHECKING_SOURCE_FILE =
	// "int_div_no_checking.cvl";
	// private Boolean check_division_by_zero = false;
	private Entity divEntity = null, modEntity = null, unsignedAddEntity = null,
			unsignedSubstractEntity = null, unsignedMultiplyEntity = null,
			signedToUnsignedEntity = null, unsignedNegEntity = null;
	private Map<String, String> macros;
	private boolean intDivProcessed = false;
	private boolean unsignedArithProcessed = false;

	// private AttributeKey intDivMacroKey;

	public IntOperationWorker(ASTFactory astFactory,
			Map<String, String> macros) {
		super(IntOperationTransformer.LONG_NAME, astFactory);
		this.identifierPrefix = "_int_div_";
		this.macros = macros;
	}

	@Override
	public AST transform(AST unit) throws SyntaxException {
		SequenceNode<BlockItemNode> root = unit.getRootNode();
		AST newAst;

		divEntity = unit.getInternalOrExternalEntity(INT_DIV);
		modEntity = unit.getInternalOrExternalEntity(INT_MOD);
		unsignedAddEntity = unit.getInternalOrExternalEntity(UNSIGNED_ADD);
		unsignedSubstractEntity = unit
				.getInternalOrExternalEntity(UNSIGNED_SUBSTRACT);
		unsignedMultiplyEntity = unit
				.getInternalOrExternalEntity(UNSIGNED_MULTIPLY);
		signedToUnsignedEntity = unit
				.getInternalOrExternalEntity(SIGNED_TO_UNSIGNED);
		unsignedNegEntity = unit.getInternalOrExternalEntity(UNSIGNED_NEG);
		if (divEntity != null || modEntity != null) {
			intDivProcessed = true;
			// return unit;
		}
		if (unsignedAddEntity != null || unsignedSubstractEntity != null
				|| unsignedMultiplyEntity != null) {
			unsignedArithProcessed = true;
		}

		if (intDivProcessed && unsignedArithProcessed)
			return unit;

		unit.release();
		if (!unsignedArithProcessed)
			linkUnsignedArithLibrary(root);
		if (!intDivProcessed)
			linkIntDivLibrary(root);
		processIntegerOperation(root);
		this.completeSources(root);
		newAst = astFactory.newAST(root, unit.getSourceFiles(),
				unit.isWholeProgram());
		// newAst.prettyPrint(System.out, false);
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
	private void processIntegerOperation(ASTNode node) {
		// if (node instanceof IdentifierExpressionNode) {
		// System.out.println("identifier node :" + node.toString() + " : "
		// + ((IdentifierExpressionNode) node).getNumConversions());
		// }

		if (node instanceof OperatorNode) {
			OperatorNode opn = (OperatorNode) node;

			// System.out.println("operatorNode:" + node.toString() + ":"
			// + opn.getOperator());
			Operator op = opn.getOperator();

			if (op == Operator.DIV || op == Operator.MOD) {
				processIntDivNode((OperatorNode) node);
			} else if (op == Operator.PLUS || op == Operator.MINUS
					|| op == Operator.TIMES) {
				processUnsignedArithNode(opn);
			} else if (op == Operator.UNARYMINUS || op == Operator.POSTINCREMENT
					|| op == Operator.PREINCREMENT) {
				processUnaryNode(opn);
			} else {
				processOtherNodes(node);
			}
		} else {
			processOtherNodes(node);
		}
	}

	private void processUnaryNode(OperatorNode opn) {
		ExpressionNode operand = opn.getArgument(0);

		if (!(operand.getConvertedType() instanceof UnsignedIntegerType))
			return;

		Operator op = opn.getOperator();
		ASTNode parent = opn.parent();
		int childIndex = opn.childIndex();
		switch (op) {
			case UNARYMINUS : {
				if (operand instanceof IntegerConstantNode) {

					String funcName = UNSIGNED_NEG;
					String method = funcName + "()";
					Source source = this.newSource(method,
							CivlcTokenConstant.CALL);
					List<ExpressionNode> args = new ArrayList<ExpressionNode>();

					opn.remove();
					args.add(opn);
					args.add(getBound());

					FunctionCallNode funcCallNode = functionCall(source,
							funcName, args);
					funcCallNode.setInitialType(opn.getConvertedType());
					parent.setChild(childIndex, funcCallNode);
				}
				break;
			}
			case POSTINCREMENT : {
				OperatorNode replacement = postIncrementReplacement(operand);
				opn.remove();
				replacement.setInitialType(opn.getConvertedType());
				parent.setChild(childIndex, replacement);
				break;
			}
			case PREINCREMENT : {
				OperatorNode replacement = preIncrementReplacement(operand);
				opn.remove();
				replacement.setInitialType(opn.getConvertedType());
				parent.setChild(childIndex, replacement);
				break;
			}
			default :
				break;
		}
	}

	private OperatorNode preIncrementReplacement(ExpressionNode operand) {
		IntegerConstantNode constantOne = null, constantZero = null,
				bound = getBound();
		OperatorNode boundMinusOneNode = null, assignedZeroNode = null,
				lessThanNode = null, preIncreNode = null, conditionNode = null;
		String one = "1", zero = "0", boundMinusOne = "bound - 1",
				assignedZero = operand.toString() + "=0",
				lessThan = operand.toString() + "<" + boundMinusOne,
				preIncre = "++" + operand.toString(),
				condition = lessThan + "?" + preIncre + ":" + assignedZero;
		Source oneSource = this.newSource(one,
				CivlcTokenConstant.INTEGER_CONSTANT);
		Source zeroSource = this.newSource(zero,
				CivlcTokenConstant.INTEGER_CONSTANT);
		Source boundMinusOneSource = this.newSource(boundMinusOne,
				CivlcTokenConstant.SUB);
		Source assignedZeroSource = this.newSource(assignedZero,
				CivlcTokenConstant.ASSIGNS);
		Source lessThanSource = this.newSource(lessThan, CivlcTokenConstant.LT);
		Source preIncreSource = this.newSource(preIncre,
				CivlcTokenConstant.PRE_INCREMENT);
		Source conditionSource = this.newSource(condition,
				CivlcTokenConstant.IF);

		try {
			constantOne = this.nodeFactory.newIntegerConstantNode(oneSource,
					one);
			constantZero = this.nodeFactory.newIntegerConstantNode(zeroSource,
					zero);
			boundMinusOneNode = this.nodeFactory.newOperatorNode(
					boundMinusOneSource, Operator.MINUS, bound, constantOne);
			assignedZeroNode = this.nodeFactory.newOperatorNode(
					assignedZeroSource, Operator.ASSIGN, operand.copy(),
					constantZero);
			lessThanNode = this.nodeFactory.newOperatorNode(lessThanSource,
					Operator.LT, operand.copy(), boundMinusOneNode.copy());
			preIncreNode = this.nodeFactory.newOperatorNode(preIncreSource,
					Operator.PREINCREMENT, operand.copy());
			conditionNode = this.nodeFactory.newOperatorNode(conditionSource,
					Operator.CONDITIONAL, lessThanNode, preIncreNode,
					assignedZeroNode);
		} catch (SyntaxException e) {
			e.printStackTrace();
		}
		return conditionNode;
	}

	private OperatorNode postIncrementReplacement(ExpressionNode operand) {
		IntegerConstantNode constantOne = null, constantZero = null,
				bound = getBound();
		OperatorNode boundMinusOneNode = null, assignedZeroNode = null,
				commaNode = null, lessThanNode = null, postIncreNode = null,
				conditionNode = null;
		String one = "1", zero = "0", boundMinusOne = "bound - 1",
				assignedZero = operand.toString() + "=0",
				comma = assignedZero + " " + boundMinusOne,
				lessThan = operand.toString() + "<" + boundMinusOne,
				postIncre = operand.toString() + "++",
				condition = lessThan + "?" + postIncre + ":" + comma;
		Source oneSource = this.newSource(one,
				CivlcTokenConstant.INTEGER_CONSTANT);
		Source zeroSource = this.newSource(zero,
				CivlcTokenConstant.INTEGER_CONSTANT);
		Source boundMinusOneSource = this.newSource(boundMinusOne,
				CivlcTokenConstant.SUB);
		Source assignedZeroSource = this.newSource(assignedZero,
				CivlcTokenConstant.ASSIGNS);
		Source commaSource = this.newSource(comma, CivlcTokenConstant.COMMA);
		Source lessThanSource = this.newSource(lessThan, CivlcTokenConstant.LT);
		Source postIncreSource = this.newSource(postIncre,
				CivlcTokenConstant.POST_DECREMENT);
		Source conditionSource = this.newSource(condition,
				CivlcTokenConstant.IF);

		try {
			constantOne = this.nodeFactory.newIntegerConstantNode(oneSource,
					one);
			constantZero = this.nodeFactory.newIntegerConstantNode(zeroSource,
					zero);
			boundMinusOneNode = this.nodeFactory.newOperatorNode(
					boundMinusOneSource, Operator.MINUS, bound, constantOne);
			assignedZeroNode = this.nodeFactory.newOperatorNode(
					assignedZeroSource, Operator.ASSIGN, operand.copy(),
					constantZero);
			commaNode = this.nodeFactory.newOperatorNode(commaSource,
					Operator.COMMA, assignedZeroNode, boundMinusOneNode);
			lessThanNode = this.nodeFactory.newOperatorNode(lessThanSource,
					Operator.LT, operand.copy(), boundMinusOneNode.copy());
			postIncreNode = this.nodeFactory.newOperatorNode(postIncreSource,
					Operator.POSTINCREMENT, operand.copy());
			conditionNode = this.nodeFactory.newOperatorNode(conditionSource,
					Operator.CONDITIONAL, lessThanNode, postIncreNode,
					commaNode);
		} catch (SyntaxException e) {
			e.printStackTrace();
		}
		return conditionNode;
	}

	private void processOtherNodes(ASTNode node) {
		// System.out.println(node.toString() + " : " +
		// node.getClass().toString());

		if (node instanceof FunctionDeclarationNode) {
			FunctionDeclarationNode funcDeclNode = (FunctionDeclarationNode) node;
			String name = funcDeclNode.getName();

			if (name.equals(INT_DIV) || name.equals(INT_MOD)
					|| name.equals(UNSIGNED_ADD)
					|| name.equals(UNSIGNED_SUBSTRACT)
					|| name.equals(UNSIGNED_MULTIPLY)
					|| name.equals(SIGNED_TO_UNSIGNED)) {
				return;
			}
		}

		for (ASTNode child : node.children()) {
			if (child != null) {
				if ((child instanceof CommonQuantifiedExpressionNode
						|| child instanceof CommonContractNode)) {
					// quantified nodes are not transformed.
					return;
				} else
					processIntegerOperation(child);
			}
		}

		// if (node instanceof IntegerConstantNode) {
		// System.out.println(node.getClass().toString());
		// System.out.println("IntegerConstantNode: "+node.toString());
		// }

		if (node instanceof ExpressionNode) {
			ExpressionNode en = (ExpressionNode) node;
			Type convertedType = null;

			if (en.getInitialType() instanceof SignedIntegerType
					&& (convertedType = en
							.getConvertedType()) instanceof StandardUnsignedIntegerType
					&& !(((StandardUnsignedIntegerType) convertedType)
							.getIntKind() == UnsignedIntKind.BOOL)) {
				System.out.println(node.getClass().toString());
				System.out.println(node.toString() + " : "
						+ en.getInitialType().getClass().toString() + " : "
						+ en.getConvertedType().getClass().toString());
				signedToUnsigned(en);
			}
		}

	}

	private void signedToUnsigned(ExpressionNode en) {
		ASTNode parent = en.parent();
		int childIndex = en.childIndex();
		String funcName = SIGNED_TO_UNSIGNED;
		String method = funcName + "()";
		Source source = this.newSource(method, CivlcTokenConstant.CALL);
		List<ExpressionNode> args = new ArrayList<ExpressionNode>();

		en.remove();
		args.add(en);
		args.add(getBound());

		FunctionCallNode funcCallNode = functionCall(source, funcName, args);
		funcCallNode.setInitialType(en.getConvertedType());
		parent.setChild(childIndex, funcCallNode);
	}

	private void processUnsignedArithNode(OperatorNode opn) {
		if (opn.getNumberOfArguments() != 2) {
			throw new CIVLSyntaxException(
					"plus , minus or substract operator can only have two operands.");
		}
		ASTNode parent = opn.parent();
		int childIndex = opn.childIndex();
		Operator op = opn.getOperator();
		ExpressionNode operand1 = opn.getArgument(0);
		ExpressionNode operand2 = opn.getArgument(1);

		processIntegerOperation(operand1);
		processIntegerOperation(operand2);
		operand1 = opn.getArgument(0);
		operand2 = opn.getArgument(1);
		// System.out.println(opn.toString() + " : " + opn.getNumConversions());
		if (operand1.getConvertedType() instanceof UnsignedIntegerType
				&& operand2.getConvertedType() instanceof UnsignedIntegerType) {
			// construct a new functionCallNode.
			String funcName = "";

			switch (op) {
				case TIMES :
					funcName = UNSIGNED_MULTIPLY;
					break;
				case PLUS :
					funcName = UNSIGNED_ADD;
					break;
				case MINUS :
					funcName = UNSIGNED_SUBSTRACT;
					break;
				default :
					break;
			}
			String method = funcName + "()";
			Source source = this.newSource(method, CivlcTokenConstant.CALL);
			List<ExpressionNode> args = new ArrayList<ExpressionNode>();

			operand1.remove();
			operand2.remove();
			args.add(operand1);
			args.add(operand2);
			args.add(getBound());

			FunctionCallNode funcCallNode = functionCall(source, funcName,
					args);

			funcCallNode.setInitialType(opn.getConvertedType());
			parent.setChild(childIndex, funcCallNode);
		}
	}

	private void processIntDivNode(OperatorNode opn) {
		if (opn.getNumberOfArguments() != 2) {
			throw new CIVLSyntaxException(
					"div or mod operator can only have two operands.");
		}

		ASTNode parent = opn.parent();
		int childIndex = opn.childIndex();
		Operator op = opn.getOperator();
		ExpressionNode operand1 = opn.getArgument(0);
		ExpressionNode operand2 = opn.getArgument(1);

		// Constant division will not be transformed.
		if (operand1.expressionKind() == ExpressionKind.CONSTANT
				&& operand2.expressionKind() == ExpressionKind.CONSTANT) {
			Value v = ((ConstantNode) operand2).getConstantValue();

			if (v.isZero() == Answer.YES)
				throw new CIVLSyntaxException("denominator can not be zero.");
			return;
		}

		processIntegerOperation(operand1);
		processIntegerOperation(operand2);
		operand1 = opn.getArgument(0);
		operand2 = opn.getArgument(1);
		if (operand1.getConvertedType() instanceof IntegerType
				&& operand2.getConvertedType() instanceof IntegerType) {
			// construct a new functionCallNode.
			String funcName = op == Operator.DIV ? INT_DIV : INT_MOD;
			String method = op == Operator.DIV
					? INT_DIV + "()"
					: INT_MOD + "()";
			Source source = this.newSource(method, CivlcTokenConstant.CALL);
			List<ExpressionNode> args = new ArrayList<ExpressionNode>();

			operand1.remove();
			operand2.remove();
			args.add(operand1);
			args.add(operand2);

			FunctionCallNode funcCallNode = functionCall(source, funcName,
					args);

			funcCallNode.setInitialType(opn.getConvertedType());
			parent.setChild(childIndex, funcCallNode);
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
	private void linkIntDivLibrary(SequenceNode<BlockItemNode> ast)
			throws SyntaxException {
		AST intDivLib;

		// if (check_division_by_zero)
		// intDivLib = this.parseSystemLibrary(new File(
		// CIVLConstants.CIVL_INCLUDE_PATH,
		// INT_DIV_NO_CHECKING_SOURCE_FILE), macros);
		// else
		intDivLib = this.parseSystemLibrary(
				new File(CIVLConstants.CIVL_INCLUDE_PATH, INT_DIV_SOURCE_FILE),
				macros);

		SequenceNode<BlockItemNode> root = intDivLib.getRootNode();
		List<BlockItemNode> funcDefinitions = new ArrayList<>();

		intDivLib.release();
		for (BlockItemNode child : root) {
			if (child instanceof FunctionDeclarationNode) {
				FunctionDeclarationNode function = (FunctionDeclarationNode) child;
				String name = function.getName();

				if (name.equals(INT_DIV) && this.divEntity == null
						|| name.equals(INT_MOD) && this.modEntity == null
						|| name.equals(ASSERT)) {
					child.remove();
					funcDefinitions.add(child);
				}
			}
		}
		ast.insertChildren(0, funcDefinitions);
	}

	private void linkUnsignedArithLibrary(SequenceNode<BlockItemNode> ast)
			throws SyntaxException {
		AST unsignedArithLib = this
				.parseSystemLibrary(new File(CIVLConstants.CIVL_INCLUDE_PATH,
						UNSIGNED_ARITH_SOURCE_FILE), macros);
		SequenceNode<BlockItemNode> root = unsignedArithLib.getRootNode();
		List<BlockItemNode> funcDefinitions = new ArrayList<>();

		unsignedArithLib.release();
		for (BlockItemNode child : root) {
			if (child instanceof FunctionDeclarationNode) {
				FunctionDeclarationNode function = (FunctionDeclarationNode) child;
				String name = function.getName();

				if (name.equals(UNSIGNED_ADD) && this.unsignedAddEntity == null
						|| name.equals(UNSIGNED_SUBSTRACT)
								&& this.unsignedSubstractEntity == null
						|| name.equals(UNSIGNED_MULTIPLY)
								&& this.unsignedMultiplyEntity == null
						|| name.equals(SIGNED_TO_UNSIGNED)
								&& this.signedToUnsignedEntity == null
						|| name.equals(UNSIGNED_NEG)
								&& this.unsignedNegEntity == null) {
					child.remove();
					funcDefinitions.add(child);
				}
			}
		}
		ast.insertChildren(0, funcDefinitions);
	}

	private IntegerConstantNode getBound() {
		IntegerConstantNode bound = null;
		long b = (1L + Integer.MAX_VALUE) * 2;
		String boundParameter = "int bound";
		Source boundSource = this.newSource(boundParameter,
				CivlcTokenConstant.PARAMETER_DECLARATION);

		try {
			bound = this.nodeFactory.newIntegerConstantNode(boundSource,
					b + "");
		} catch (SyntaxException e) {
			e.printStackTrace();
		}
		return bound;
	}

}
