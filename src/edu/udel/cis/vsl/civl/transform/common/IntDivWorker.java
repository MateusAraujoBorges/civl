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
import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.front.IF.CivlcTokenConstant;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.transform.IF.IntDivisionTransformer;

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

	/* *******************static constants************************ */
	// TODO add java doc for every constant field
	private static final String INT_DIV = "$int_div";
	private static final String INT_MOD = "$int_mod";
	private static final String INT_DIV_SOURCE_FILE = "int_div.cvl";

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
		if(divEntity != null && modEntity != null){
			return unit;
		}
		
//		for (BlockItemNode child : root) {
//			if (child instanceof FunctionDefinitionNode) {
//				String funcName = ((FunctionDefinitionNode) child).getName();
//
//				// if the ast already contains $int_div or $int_mod definition,
//				// then no transformation is needed, because $int_div and
//				// $int_mod are invisible to users. If they are present, then
//				// this ast is the result of all CIVL-C transformation.
//				if (funcName.equals(INT_MOD) || funcName.equals(INT_DIV))
//					return unit;
//			}
//		}
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
			// and $int_mod
			// functions should not be replaced.
			FunctionDeclarationNode funcDeclNode = (FunctionDeclarationNode) node;
			String name = funcDeclNode.getName();

			if (name.equals(INT_DIV) || name.equals(INT_MOD))
				return;
		}
		if (node instanceof OperatorNode && (((OperatorNode) node).getOperator() == Operator.DIV
				|| ((OperatorNode) node).getOperator() == Operator.MOD)) {
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
				if (child != null)
					processDivisionAndModulo(child);
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
		AST intDivLib = this.parseSystemLibrary(INT_DIV_SOURCE_FILE);
		SequenceNode<BlockItemNode> root = intDivLib.getRootNode();
		List<BlockItemNode> funcDefinitions = new ArrayList<>();

		intDivLib.release();
		for (BlockItemNode child : root) {
			child.remove();
			funcDefinitions.add(child);
		}
		ast.insertChildren(0, funcDefinitions);
	}
}
