package edu.udel.cis.vsl.civl.statistical;

import edu.udel.cis.vsl.gmc.util.BigRational;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.nio.charset.StandardCharsets;

public class PCPConnectionManager implements ConnectionManager {
	private int pid;
	private Socket countServer;
	private OutputStreamWriter out;
	private BufferedReader in;

	public PCPConnectionManager(String serverAddress, int serverPort, int pid) throws IOException {
		// Initialize connection
		this.countServer = new Socket(serverAddress, serverPort);
		this.out = new OutputStreamWriter(countServer.getOutputStream(), StandardCharsets.UTF_8);
		this.in = new BufferedReader(new InputStreamReader(countServer.getInputStream()));
		this.pid = pid;
	}

	@Override
	public CountResult count(String query) {
		try {
			// logger.log(Level.INFO, "[pcpV2] query sent: \n " +
			// query.replaceAll("\n", "\n "));
			out.write(query, 0, query.length());
			out.flush();
			String response = in.readLine();
			if (response == null || response.isEmpty()) {
				throw new RuntimeException("The count server returned an null/empty string");
			} else if (response.contains("error")) {
				throw new RuntimeException("The count server returned an error: " + response);
			} else {
				// merge multiple whitespaces
				response = response.substring(1, response.length() - 1)
								.replaceAll("\\s+", " ");
				System.out.println("[PCPCounter] result:\"" + response + "\"");
				String[] toks = response.split(" ");
				BigRational prob;
				BigRational var;

				if (toks[0].equals("exact:")) {
					prob = new BigRational(toks[1]);
					var = BigRational.ZERO;
				} else if (toks[0].equals("statistical:")) {
					prob = new BigRational(toks[1]);
					var = new BigRational(toks[3]);
				} else {
					throw new RuntimeException("Unknown count type! " + response);
				}

				System.out.println("[pcCounter] successful count received: pr="
								+ prob + " var=" + var);
				return new StatisticalCountResult(prob, var);
			}
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	@Override
	public void close() throws IOException {
		this.out.close();
		this.in.close();
		this.countServer.close();
	}

	@Override
	public int getPID() {
		return pid;
	}
}
