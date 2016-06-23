package edu.udel.cis.vsl.civl.slice.common;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

public class FlowGraph {
	
	protected List<Vertex> vertices;
	protected Set<Arc> arcs;
	protected Vertex entryVertex;
	protected Set<Arc> exitArcs;
	protected Map<Vertex,Set<Vertex>> succMap;
	
	protected FlowGraph(CIVLFunction f, Map<Variable, Set<Variable>> formalToActualMap) {
		this.vertices = new ArrayList<Vertex>();
		this.arcs = new HashSet<Arc>();
		this.exitArcs = new HashSet<Arc>();
		
		Set<Location> locs = f.locations();
		Set<Statement> stmts = f.statements();
		
		Map<Location,Vertex> locationVertexMap = new HashMap<Location, Vertex>();
		Map<Statement,Arc> statementArcMap = new HashMap<Statement,Arc>();
		
		for (Location l : locs) {
			Vertex v = new Vertex(l);
			this.vertices.add(v);
			locationVertexMap.put(l,v);
		}
		for (Statement s : stmts) {
			Arc a = new Arc(s);
			this.arcs.add(a);
			statementArcMap.put(s,a);
		}
	    this.entryVertex = this.vertices.get(0);
		for (Vertex v : this.vertices) {
			/* Discover incoming an outgoing Arcs (Statements) */
			for (Statement s : v.location.incoming()) v.in.add(statementArcMap.get(s));
			for (Statement s : v.location.outgoing()) v.out.add(statementArcMap.get(s));
			System.out.println("************* "+v+" in set is: "+v.in);
		}
		for (Arc a : this.arcs) {
			/* Discover source and target Vertices (Locations) */
			a.source = locationVertexMap.get(a.statement.source());
			a.target = locationVertexMap.get(a.statement.target());
			if (a.statement.toString().equals("$havoc(&(temp))")) {
				assert a.target != null;
			}
			if (a.statement.statementKind() == Statement.StatementKind.RETURN) { 
				this.exitArcs.add(a);
			}
			/* Set reference to formal->actual parameters map */
			a.formalToActualMap = formalToActualMap;
			
			//System.out.println("Arc :"+a+" has statement kind: "+a.statement.statementKind());
		}
		this.succMap = new HashMap<Vertex,Set<Vertex>>();
		for (Vertex v : this.vertices) {
			Set<Vertex> succs = new HashSet<Vertex>();
			for (Arc a : v.out) {
				succs.add(a.target);
			}
			succMap.put(v, succs);
		}
	}

}
