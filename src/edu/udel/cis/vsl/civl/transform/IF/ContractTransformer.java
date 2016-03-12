package edu.udel.cis.vsl.civl.transform.IF;

import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AssignStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement.StatementKind;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public abstract class ContractTransformer extends Transforms {
	public abstract Model transformObjectFunction(Model porgram,
			CIVLFunction function);

	static public List<AssignStatement> getGlobalStatements(Model program) {
		CIVLFunction system = program.system();
		Location location = system.startLocation();
		Deque<Location> locStack = new LinkedList<>();
		List<AssignStatement> result = new LinkedList<>();
		Scope rootScope = system.outerScope();

		// traverse the whole system function to get all assign statements:
		locStack.add(location);
		while (!locStack.isEmpty()) {
			Location currLoc = locStack.pop();
			Iterator<Statement> stmtIter = currLoc.outgoing().iterator();

			while (stmtIter.hasNext()) {
				Statement stmt = stmtIter.next();
				Location target = stmt.target();

				if (stmt.statementKind().equals(StatementKind.ASSIGN)) {
					AssignStatement assignment = (AssignStatement) stmt;
					LHSExpression lhs = assignment.getLhs();
					Variable var = lhs.variableWritten();

					if (var.scope().id() == rootScope.id())
						result.add(assignment);
				}
				if (target != null)
					locStack.add(target);
			}
		}
		return result;
	}
}
