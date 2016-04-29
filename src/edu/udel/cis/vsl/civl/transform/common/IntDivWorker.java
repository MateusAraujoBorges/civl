package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.List;
import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.type.IF.Types;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.front.IF.CivlcTokenConstant;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.transform.IF.IntDivisionTransformer;

public class IntDivWorker extends BaseWorker{
	
	public IntDivWorker(ASTFactory astFactory) {
		super(IntDivisionTransformer.LONG_NAME, astFactory);
		this.identifierPrefix = "_int_div_";
	}

	@Override
	public AST transform(AST unit) throws SyntaxException {
		SequenceNode<BlockItemNode> root = unit.getRootNode();
		AST newAst;
		
		unit.release();
		linkIntDivLibrary(root);
		processDivisionAndModulo(root);
		this.completeSources(root);
		newAst = astFactory.newAST(root, unit.getSourceFiles(),
				unit.isWholeProgram());
		return newAst;
	}
	
	/**
	 * Process DIV and MOD operator node, replace each div and mod operator with
	 * corresponding function define in civlc lib.
	 * 
	 * @param node
	 */
	private void processDivisionAndModulo(ASTNode node){
		if(node instanceof FunctionDeclarationNode){
			FunctionDeclarationNode funcDeclNode = (FunctionDeclarationNode)node;
			IdentifierNode idNode = (IdentifierNode)funcDeclNode.child(0);
			
			if(idNode.name().equals("$int_div")
					|| idNode.name().equals("$int_mod"))
				return;
		}
		if (node instanceof OperatorNode
				&& (((OperatorNode)node).getOperator() == Operator.DIV
				|| ((OperatorNode)node).getOperator() == Operator.MOD)) {
			OperatorNode opn = (OperatorNode)node;
			
			if(opn.getNumberOfArguments() != 2) {
				throw new CIVLSyntaxException(
						"div or mod operator can only have two operands");
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
			if(operand1.getInitialType().equivalentTo(
					Types.newTypeFactory().basicType(BasicTypeKind.INT)) && 
			   operand2.getInitialType().equivalentTo(
					Types.newTypeFactory().basicType(BasicTypeKind.INT))) {
				/**
				 * construct a new functionCallNode.
				 */
				String funcName = (op == Operator.DIV) ? "$int_div" : "$int_mod";
				String method = (op == Operator.DIV) ? "$int_div()" : "$int_mod()";
				Source source = this.newSource(method, CivlcTokenConstant.CALL);
				IdentifierNode idNode = nodeFactory.newIdentifierNode(source, funcName);
				IdentifierExpressionNode funcIdentifier = 
						nodeFactory.newIdentifierExpressionNode(source, idNode);
				List<ExpressionNode> args = new ArrayList<ExpressionNode>();
				
				args.add(operand1.copy());
				args.add(operand2.copy());
				FunctionCallNode funcCallNode = nodeFactory.newFunctionCallNode(
						source, funcIdentifier, args, null); 
				
				funcCallNode.setInitialType(Types.newTypeFactory().basicType(BasicTypeKind.INT));
				node.remove();
				parent.setChild(childIndex, funcCallNode);
			}
		} else {
			for (ASTNode child : node.children()) {
				if (child != null)
					processDivisionAndModulo(child);
			}
		}
	}
	
	private void linkIntDivLibrary(SequenceNode<BlockItemNode> ast){
		try {
			AST intDivLib = this.parseSystemLibrary("int_div.cvl");
			SequenceNode<BlockItemNode> root = intDivLib.getRootNode();
//			System.out.println("children #:"+ root.numChildren());
//			System.out.println("root children:"+ root.children());
			List<BlockItemNode> funcDefinitions = new ArrayList<>();
			
			for (ASTNode child : root.children()){
				if(child instanceof FunctionDefinitionNode){
					funcDefinitions.add((FunctionDeclarationNode)child.copy());
				}else{
					if(child instanceof FunctionDeclarationNode){
						FunctionDeclarationNode funcDeclNode = (FunctionDeclarationNode)child;
						
						if(funcDeclNode.getIdentifier().name().equals("$assert")){
							funcDefinitions.add((FunctionDeclarationNode)child.copy());
						}
					}
				}
			}
			ast.insertChildren(0, funcDefinitions);
		} catch (SyntaxException e) {
			e.printStackTrace();
		}
	}

}
