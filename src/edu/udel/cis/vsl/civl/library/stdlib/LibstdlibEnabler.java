package edu.udel.cis.vsl.civl.library.stdlib;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEnabler;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;

/**
 * Implementation of the enabler-related logics for system functions declared
 * stdlib.h.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class LibstdlibEnabler extends BaseLibraryEnabler implements
		LibraryEnabler {

	/* **************************** Constructors *************************** */

	/**
	 * Creates a new instance of the library enabler for stdlib.h.
	 * 
	 * @param primaryEnabler
	 *            The enabler for normal CIVL execution.
	 * @param output
	 *            The output stream to be used in the enabler.
	 * @param modelFactory
	 *            The model factory of the system.
	 */
	public LibstdlibEnabler(String name, Enabler primaryEnabler,
			Evaluator evaluator, ModelFactory modelFactory,
			SymbolicUtility symbolicUtil) {
		super(name, primaryEnabler, evaluator, modelFactory, symbolicUtil);
	}
}
