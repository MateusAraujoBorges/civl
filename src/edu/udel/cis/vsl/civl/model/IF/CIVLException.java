package edu.udel.cis.vsl.civl.model.IF;

/**
 * Root of CIVL exception hierarchy, representing any kind of event where
 * something goes wrong in CIVL.
 * 
 * @author siegel
 * 
 */
public class CIVLException extends RuntimeException {

	/**
	 * Generated by Eclipse.
	 */
	private static final long serialVersionUID = -5218392349059280169L;

	/**
	 * A certainty level gages how certain we are that this is error is a real
	 * error, i.e., not just a spurious error.
	 * 
	 * There are 3 levels, from highest to lowest level of certainty.
	 * 
	 * @author siegel
	 * 
	 */
	public enum Certainty {
		/**
		 * A concrete trace verifies this is an error: the highest level of
		 * certainty that this represents a real error in the program being
		 * analyzed.
		 */
		CONCRETE,
		/**
		 * A theorem prover says this is an error: second-highest level of
		 * certainty. However no conrete trace has been produced to verify the
		 * theorem prover's claim.
		 */
		PROVEABLE,
		/**
		 * The prover is not sure whether this is an error. It could be due to
		 * the incompleteness of the decision procecure, or it could be a real
		 * error.
		 */
		MAYBE,
		/**
		 * Probably an internal CIVL error: the theorem prover hasn't said
		 * anything. The lowest level of certaintly that this represents a real
		 * error in the program being analyzed.
		 */
		NONE
	}

	public enum ErrorKind {
		ARRAY_DECLARATION, ASSERTION_VIOLATION, COMMUNICATION, CONSTANT_WRITE, CONTRACT,
		CYCLE, DEADLOCK, DEREFERENCE, DIVISION_BY_ZERO, FUNCTIONAL_COMPATIBILITY,
		INPUT_WRITE, INT_DIVISION, INTERNAL, INVALID_CAST, INVALID_PID, INVARIANT_VIOLATION, 
		LIBRARY, MALLOC, MEMORY_LEAK, MPI_ERROR, OTHER, OUT_OF_BOUNDS, OUTPUT_READ,
		POINTER, QUANTIFIER, PRINTF, SIZEOF, INVALID_WAIT, UNDEFINED_VALUE, UNION, 
		PROCESS_LEAK, SEQUENCE, FUNCTIONAL_EQUIVALENCE
	}

	/**
	 * Source of the element that led to exception, for error reporting. May be
	 * null.
	 */
	protected CIVLSource source;

	public CIVLException(String message, CIVLSource source) {
		super(message);
		assert message != null;
		this.source = source;
	}

	@Override
	public String toString() {
		String result = getMessage();

		if (source != null)
			result += "\nat " + source.getSummary() + ".";
		return result;
	}

	/**
	 * @return the source code element associated with this exception
	 */
	public CIVLSource getSource() {
		return source;
	}

}
