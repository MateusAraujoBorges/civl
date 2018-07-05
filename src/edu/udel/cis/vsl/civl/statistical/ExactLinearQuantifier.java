package edu.udel.cis.vsl.civl.statistical;

import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.gmc.seq.StateQuantifier;
import edu.udel.cis.vsl.gmc.util.BigRational;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.preuniverse.IF.PreUniverse;
import edu.udel.cis.vsl.sarl.prove.z3.PCPTranslator;
import edu.udel.cis.vsl.sarl.util.FastList;

import java.io.IOException;
import java.io.PrintStream;

public class ExactLinearQuantifier implements StateQuantifier<State> {

	private final SymbolicUniverse universe;
	private final PrintStream debug;
	private final PCPConnectionManager pcp;


	public ExactLinearQuantifier(SymbolicUniverse universe, PrintStream debug) throws IOException {
		this.universe = universe;
		this.pcp = new PCPConnectionManager("localhost", 9001, -1);
		this.debug = debug;
	}

	@Override
	public BigRational quantify(State state) {
		BooleanExpression pc = state.getPathCondition(universe);
		PCPTranslator translator = new PCPTranslator((PreUniverse) universe, pc, false);

		StringBuilder query = new StringBuilder();
		query.append("(clear)\n");
		query.append("(set-option :non-linear-counter \"qcoral\")\n" +
						"(set-option :partitioning true)\n");

		FastList<String> declarations = translator.getDeclarations();
		FastList<String> translatedPC = translator.getTranslation();

		if (declarations.isEmpty() && translatedPC.toString().equals("true")) {
			return BigRational.ONE;
		}

		if (!declarations.isEmpty()) {
			query.append(translator.getDeclarations());
		}

		query.append("(assert ");
		query.append(translator.getTranslation());
		query.append(")\n");
		query.append("(count)\n");

		if (debug != null) {
			debug.printf("[exactLinearQ] query:\n%s\n", query);
		}
		CountResult result = pcp.count(query.toString());
		if (debug != null) {
			debug.printf("[exactLinearQ] result: %s \n", result);
		}
		return result.getMean();
	}

}
