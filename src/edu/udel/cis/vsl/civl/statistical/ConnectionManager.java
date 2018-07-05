package edu.udel.cis.vsl.civl.statistical;

import java.io.IOException;

public interface ConnectionManager {
	CountResult count(String query);

	void close() throws IOException;

	int getPID();
}

