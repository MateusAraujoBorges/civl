package edu.udel.cis.vsl.civl.model.common;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.LogicFunction;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class CommonLogicFunction extends CommonFunction
		implements
			LogicFunction {

	/**
	 * {@linkplain ACSLPredicate#definition()}
	 */
	private final Expression definition;

	public CommonLogicFunction(CIVLSource source, Identifier name,
			Scope parameterScope, List<Variable> parameters,
			Scope containingScope, int fid, ModelFactory factory,
			Expression definition) {
		super(source, true, name, parameterScope, parameters,
				factory.typeFactory().booleanType(), containingScope, fid,
				factory.location(source, parameterScope), factory);
		this.definition = definition;
	}

	@Override
	public Expression definition() {
		return definition;
	}

	@Override
	public int hashCode() {
		// no over-loading, so parameters are not part of the hash:
		return definition.hashCode() ^ this.name().hashCode() ^ 897653;
	}
}
