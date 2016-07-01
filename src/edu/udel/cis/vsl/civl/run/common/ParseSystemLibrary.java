package edu.udel.cis.vsl.civl.run.common;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.main.ABCExecutor;
import edu.udel.cis.vsl.abc.main.DynamicTask;
import edu.udel.cis.vsl.abc.main.UnitTask;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;

public class ParseSystemLibrary implements DynamicTask {

	private ABCExecutor executor;

	public ParseSystemLibrary(ABCExecutor executor) {
		this.executor = executor;
	}

	private Set<String> getExistingFiles() {
		int num = executor.getNumCompleteUnitTasks();
		Set<String> fileNames = new HashSet<>();

		for (int i = 0; i < num; i++) {
			AST ast = executor.getAST(i);
			Collection<SourceFile> files = ast.getSourceFiles();

			for (SourceFile file : files) {
				String filename = file.getName();

				fileNames.add(filename);
			}
		}
		return fileNames;
	}

	@Override
	public UnitTask[] generateTasks() {
		int num = executor.getNumCompleteUnitTasks();
		List<UnitTask> result = new ArrayList<>();
		Set<String> existingFiles = getExistingFiles();
		Set<String> processedFiles = new HashSet<>();

		for (int i = 0; i < num; i++) {
			AST ast = executor.getAST(i);
			Collection<SourceFile> files = ast.getSourceFiles();

			for (SourceFile file : files) {
				String filename = file.getName();

				if (!processedFiles.add(filename))
					continue;

				File systemFile = getSystemImplementation(file.getFile());

				if (systemFile != null) {
					String systemFilename = systemFile.getName();

					if (!existingFiles.contains(systemFilename)
							&& processedFiles.add(systemFilename)) {
						result.add(new UnitTask(new File[] { systemFile }));
					}
				}
			}
		}
		UnitTask[] tasks = new UnitTask[result.size()];
		return result.toArray(tasks);
	}

	/**
	 * Finds out the file name of the system implementation of a header file,
	 * which stands for a certain system library, such as civlc.cvh, mpi.h,
	 * omp.h, stdio.h, etc.
	 * 
	 * @param file
	 * @return The file name of the system implementation of the given header
	 *         file, or null if there is no implementation of the header file.
	 */
	private File getSystemImplementation(File file) {
		String name = file.getName();

		if (CIVLConstants.getAllCivlLibs().contains(name))
			return new File(CIVLConstants.CIVL_INCLUDE_PATH, name.substring(0,
					name.length() - 1) + "l");
		else if (CIVLConstants.getCinterfaces().contains(name))
			return new File(CIVLConstants.CIVL_INCLUDE_PATH, name.substring(0,
					name.length() - 1) + "cvl");
		return null;
	}

}
