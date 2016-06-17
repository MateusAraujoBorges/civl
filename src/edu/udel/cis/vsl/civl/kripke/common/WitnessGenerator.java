package edu.udel.cis.vsl.civl.kripke.common;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import edu.udel.cis.vsl.civl.kripke.IF.AtomicStep;
import edu.udel.cis.vsl.civl.kripke.IF.TraceStep;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.gmc.Trace;
import edu.udel.cis.vsl.gmc.TraceStepIF;

/**
 * SV-COMP requires a "witness" to be generated for a violation
 * of any property.
 * 
 * The witness of a property violation found by CIVL is a way
 * to tell other program analyzers the path that CIVL took in
 * finding that violation.  The common interface for path guidance
 * is given by a control flow automata---called an error automata---, 
 * which is the dual of a control flow graph, i.e., the nodes represent
 * program locations and the edges represent program statements.
 * Error automata nodes are annotated with the source code line number, and the 
 * edges connecting the nodes are annotated with the source code of the
 * executed statement (in a brittle and underspecified way, see the specs: 
 * https://sv-comp.sosy-lab.org/2016/witnesses/).  The witness is specified 
 * in the GraphML language, which is an extension of XML for describing 
 * graphs.
 * 
 * The error automata is essentially CIVL's transition system, 
 * where edges are annotated with CIVL {@link Statement}s, and nodes are 
 * CIVL {@link Location}s.  The only difference is that there is a specified 
 * "entry" node and a final "violation" node.  
 * 
 * The beginning node must be of the form:
 *   
 *   <node id="Location0">
 *     <data key="entry">true</data>
 *   </node>
 *   
 * and the node leading to the error of the form:
 *   
 *   <node id="Location24">
 *     <data key="violation">true</data>
 *   </node>
 *   
 * We step through a CIVL {@link Trace} and name nodes according to 
 * their {@link Location} string (with whitespace stripped), like:
 *   
 *   <node id="Location1"/>
 *   
 * and the edges according to their {@link Statement} string, like:
 * 
 *   <edge source="Location1" target="Location2">
 *     <data key="sourcecode">int x=0;</data>
 *     <data key="startline">10</data>
 *   </edge>
 *   
 * Any edge ({@link Statement}) of a conditional branch must also include 
 * the one of the data elements:
 * 
 *   <data key="control">condition-false</data>
 *   
 * or
 * 
 *   <data key="control">condition-true</data>
 * 
 * @author mgerrard
 *
 */

public class WitnessGenerator {
	
	public WitnessGenerator (Model model, Trace<Transition, State> trace) throws IOException {
		List<TraceStepIF<Transition, State>> steps = trace.traceSteps();
		Iterator<TraceStepIF<Transition, State>> it = steps.iterator();
		List<Pair<Location,Statement>> traceStepLocStmt = traceLocStmtPairs(it);
		
		System.out.println(header());
		
		String finalLocation = "";
		for(Pair<Location,Statement> step : traceStepLocStmt) {
			Location location = step.left; Statement statement = step.right;
			String locationStr = location.toString(); String statementStr = statement.toString();
			/* We need to strip the whitespace from the Location strings */
			String compactSourceStr = locationStr.replaceAll("\\s+","");
			String compactTargetStr = statement.target().toString().replaceAll("\\s+","");
			
			if (!locationStr.equals("Location 0")) { // Location 0 is hard-coded into the header
				if (statementStr.equals("__VERIFIER_error()")) {
					System.out.println("<node id=\""+compactSourceStr+"\">\n"
							+ "  <data key=\"violation\">true</data>\n"
							+ "</node>");
					System.out.println("<node id=\""+compactTargetStr+"\"/>");
				} else {
					System.out.println("<node id=\""+compactSourceStr+"\"/>");
				}
			}
			String sourceLocationStr = step.left.getSource().getLocation().toString();
			if (sourceLocationStr.matches(".*.c:.*")) {
			   String lineNumber = sourceLocationStr.replaceAll(".*:([0-9]+)..*", "$1");
			   
			   if (statementStr.equals("FALSE_BRANCH_IF")) {
				    System.out.println("<edge source=\""+compactSourceStr+"\" target=\""+compactTargetStr+"\">");
				    System.out.println("  <data key=\"sourcecode\">["+statement.guard()+"]</data>");
				    System.out.println("  <data key=\"startline\">"+lineNumber+"</data>");
				    System.out.println("  <data key=\"control\">condition-false</data>");
				    System.out.println("</edge>");
			   } else if (statementStr.equals("TRUE_BRANCH_IF")){
				   	System.out.println("<edge source=\""+compactSourceStr+"\" target=\""+compactTargetStr+"\">");
				    System.out.println("  <data key=\"sourcecode\">["+statement.guard()+"]</data>");
				    System.out.println("  <data key=\"startline\">"+lineNumber+"</data>");
				    System.out.println("  <data key=\"control\">condition-false</data>");
				    System.out.println("</edge>");
			   } else {
				    System.out.println("<edge source=\""+compactSourceStr+"\" target=\""+compactTargetStr+"\">");
				    System.out.println("  <data key=\"sourcecode\">"+statement+"</data>");
				    System.out.println("  <data key=\"startline\">"+lineNumber+"</data>");
				    System.out.println("</edge>");
			   }
			} else {
				System.out.println("<edge source=\""+compactSourceStr+"\" target=\""+compactTargetStr+"\"/>");
			}
			
			finalLocation = compactTargetStr;
		}
		System.out.println("<node id=\""+finalLocation+"\"/>");
		
		System.out.println(footer());
	}
	
	/* Extract Location-Statement pairs from TraceStep Iterator */
	private List<Pair<Location, Statement>> traceLocStmtPairs(
			Iterator<TraceStepIF<Transition, State>> it) {
		List<Pair<Location, Statement>> tracePairs = new ArrayList<Pair<Location, Statement>>();
		while(it.hasNext()) {
			TraceStep step = ((TraceStep) it.next());
			Iterable<AtomicStep> atomicSteps = step.getAtomicSteps();
			for(AtomicStep atom : atomicSteps){
				Location l = atom.getStatement().source();
				Statement s = atom.getStatement();
				tracePairs.add(new Pair<Location,Statement>(l,s));
			}
		}
		return tracePairs;
	}
	
	private String header() {
		return "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\r\n"
				+ "<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\">\r\n "
				+ "<key attr.name=\"invariant\" attr.type=\"string\" for=\"node\" id=\"invariant\"/>\r\n "
				+ "<key attr.name=\"invariant.scope\" attr.type=\"string\" for=\"node\" id=\"invariant.scope\"/>\r\n "
				+ "<key attr.name=\"namedValue\" attr.type=\"string\" for=\"node\" id=\"named\"/>\r\n "
				+ "<key attr.name=\"nodeType\" attr.type=\"string\" for=\"node\" id=\"nodetype\">\r\n  "
				+ "<default>path</default>\r\n "
				+ "</key>\r\n "
				+ "<key attr.name=\"isFrontierNode\" attr.type=\"boolean\" for=\"node\" id=\"frontier\">\r\n  "
				+ "<default>false</default>\r\n "
				+ "</key>\r\n "
				+ "<key attr.name=\"isViolationNode\" attr.type=\"boolean\" for=\"node\" id=\"violation\">\r\n  "
				+ "<default>false</default>\r\n </key>\r\n "
				+ "<key attr.name=\"isEntryNode\" attr.type=\"boolean\" for=\"node\" id=\"entry\">\r\n  "
				+ "<default>false</default>\r\n "
				+ "</key>\r\n "
				+ "<key attr.name=\"isSinkNode\" attr.type=\"boolean\" for=\"node\" id=\"sink\">\r\n  "
				+ "<default>false</default>\r\n "
				+ "</key>\r\n "
				+ "<key attr.name=\"isLoopHead\" attr.type=\"boolean\" for=\"node\" id=\"loopHead\">\r\n  "
				+ "<default>false</default>\r\n "
				+ "</key>\r\n "
				+ "<key attr.name=\"violatedProperty\" attr.type=\"string\" for=\"node\" id=\"violatedProperty\"/>\r\n "
				+ "<key attr.name=\"threadId\" attr.type=\"string\" for=\"edge\" id=\"threadId\"/>\r\n "
				+ "<key attr.name=\"sourcecodeLanguage\" attr.type=\"string\" for=\"graph\" id=\"sourcecodelang\"/>\r\n "
				+ "<key attr.name=\"programFile\" attr.type=\"string\" for=\"graph\" id=\"programfile\"/>\r\n "
				+ "<key attr.name=\"programHash\" attr.type=\"string\" for=\"graph\" id=\"programhash\"/>\r\n "
				+ "<key attr.name=\"specification\" attr.type=\"string\" for=\"graph\" id=\"specification\"/>\r\n "
				+ "<key attr.name=\"memoryModel\" attr.type=\"string\" for=\"graph\" id=\"memorymodel\"/>\r\n "
				+ "<key attr.name=\"architecture\" attr.type=\"string\" for=\"graph\" id=\"architecture\"/>\r\n "
				+ "<key attr.name=\"producer\" attr.type=\"string\" for=\"graph\" id=\"producer\"/>\r\n "
				+ "<key attr.name=\"sourcecode\" attr.type=\"string\" for=\"edge\" id=\"sourcecode\"/>\r\n "
				+ "<key attr.name=\"startline\" attr.type=\"int\" for=\"edge\" id=\"startline\"/>\r\n "
				+ "<key attr.name=\"startoffset\" attr.type=\"int\" for=\"edge\" id=\"startoffset\"/>\r\n "
				+ "<key attr.name=\"lineColSet\" attr.type=\"string\" for=\"edge\" id=\"lineCols\"/>\r\n "
				+ "<key attr.name=\"control\" attr.type=\"string\" for=\"edge\" id=\"control\"/>\r\n "
				+ "<key attr.name=\"assumption\" attr.type=\"string\" for=\"edge\" id=\"assumption\"/>\r\n "
				+ "<key attr.name=\"assumption.scope\" attr.type=\"string\" for=\"edge\" id=\"assumption.scope\"/>\r\n "
				+ "<key attr.name=\"enterFunction\" attr.type=\"string\" for=\"edge\" id=\"enterFunction\"/>\r\n "
				+ "<key attr.name=\"returnFromFunction\" attr.type=\"string\" for=\"edge\" id=\"returnFrom\"/>\r\n "
				+ "<key attr.name=\"predecessor\" attr.type=\"string\" for=\"edge\" id=\"predecessor\"/>\r\n "
				+ "<key attr.name=\"successor\" attr.type=\"string\" for=\"edge\" id=\"successor\"/>\r\n "
				+ "<key attr.name=\"witness-type\" attr.type=\"string\" for=\"graph\" id=\"witness-type\"/>\r\n "
				+ "<graph edgedefault=\"directed\">\r\n  <data key=\"witness-type\">violation_witness</data>\r\n  "
				+ "<data key=\"sourcecodelang\">C</data>\r\n  <data key=\"producer\">CIVL</data>\r\n "
				+ "<data key=\"specification\">CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )</data>\r\n "
				+ "<data key=\"memorymodel\">precise</data>\r\n  <data key=\"architecture\">32bit</data>\r\n  "
				+ "<node id=\"Location0\">\r\n"
				+ "   <data key=\"entry\">true</data>\r\n  "
				+ "</node>";
	}
	
	private String footer() {
		return " </graph>\r\n"
				+ "</graphml>";
	}

}
