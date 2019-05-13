package test;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import communication.Server;

/**
 * To test the Server and mostly the ClientHandler this Test is used to create a 2 
 * minute server that can be connected to by running Clients and connecting to this server.
 * Put in appropriate test cases by trying different input on the Client side to test the behavior
 * of the ClientHandler, after the server has closed the coverage of the test can be seen.
 * This requires the use of Emma for example. 
 * @author Corjan van den Brink
 * @version 2019.01.31
 */
class ServerTest {

	Server server;
	int min = 2; // change this for longer testing time
	
	@BeforeEach
	void setUp() throws Exception {
		server = new Server(2727);
		server.start();
	}

	@AfterEach
	void tearDown() throws Exception {
	}

	@Test
	void test() {
		try {
			server.join(min * 1000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		server.closeServer();
	}

}
