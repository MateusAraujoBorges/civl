package edu.udel.cis.vsl.civl.library.collate;

import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;

/**
 * This class reserves the structure information for datatypes in the collate
 * library
 * 
 * @author ziqing
 *
 */
public class LibcollateConstants {

	static public final int GCOLLATOR_NPROCS = 0;
	static public final int GCOLLATOR_PROCS = 1;
	static public final int GCOLLATOR_QUEUE_LENGTH = 2;
	static public final int GCOLLATOR_QUEUE = 3;
	static public final int COLLATOR_PLACE = 0;
	static public final int COLLATOR_GCOLLATOR = 1;
	static public final int GCOLLATE_STATE_STATUS = 0;
	static public final int GCOLLATE_STATE_STATE = 1;
	static public final int COLLATE_STATE_PLACE = 0;
	static public final int COLLATE_STATE_GSTATE = 1;

	static public CIVLType gcollate_state(CIVLTypeFactory typeFactory) {
		return typeFactory.systemType(ModelConfiguration.GCOLLATOR_TYPE);
	}

	static public CIVLType collate_state(CIVLTypeFactory typeFactory) {
		return typeFactory.systemType(ModelConfiguration.COLLATOR_TYPE);
	}

}
