package edu.udel.cis.vsl.civl.model.IF.expression.contracts;

import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

public interface ObligationClause extends Expression, ContractClause {
	Expression getBody();
}
