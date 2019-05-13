package test;

import communication.*;
import controller.InvalidIndexException;
import model.Board;
import model.Move;
import model.MoveType;
import model.RotatableTile;
import model.Rotation;

import static org.junit.jupiter.api.Assertions.*;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.Random;
import java.util.Scanner;
import java.util.List;

import org.junit.After;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Testing class for Client.
 * @author Corjan van den Brink
 * @version 2019.01.31
 */
class ClientTest {
	
	/*
	 * Client testing is done using a mockup server in which the streams are used for communication.
	 * Parts of the Client that are tested are mostly based on seeing whether the Client reacts to
	 * the protocol as we'd expect.
	 */
	
	Client clientA;
	int port = 2727;
	InetAddress host = null;
	ServerSocket server;
	BufferedWriter chout;
	BufferedReader chin;
	Socket s;

	/**
	 * Creates a ServerSocket for catching all communication from a Client.
	 * @throws Exception
	 */
	@BeforeEach
	void setUp() throws Exception {
		host = InetAddress.getLocalHost();
		server = new ServerSocket(port, 4, host);
	}

	/**
	 * Test creating a Client with a computer player and setting up the streams.
	 */
	@Test
	void testInit() {
		String name = "player" + (new Random()).nextInt();
		try {
			clientA = new Client(host, port, name, "computer-naive");
			clientA.start();
			s = server.accept();
			chin = new BufferedReader(new InputStreamReader(s.getInputStream()));
	    	chout = new BufferedWriter(new OutputStreamWriter(s.getOutputStream()));
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		assertTrue(clientA.getClientName().equals(name));
		
	}
	
	/**
	 * Creates a client and test if sending the features works, sets a custom feature 
	 * that should be caught server side.
	 */
	@Test
	void testFeatures() {
		try {
			String feature = "Extension";
			Client.clientFeatures = new String[] {feature};
			clientA = new Client(host, port, "player" + (new Random()).nextInt(), "human");
			clientA.start();
			s = server.accept();
			chin = new BufferedReader(new InputStreamReader(s.getInputStream()));
	    	chout = new BufferedWriter(new OutputStreamWriter(s.getOutputStream()));
			sendMessage(Protocol.SERVERFEATURES);
			String resp = chin.readLine();
			assertTrue(resp.startsWith(Protocol.CLIENTFEATURES));
			assertTrue(resp.endsWith(feature));
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}		
	}
	
	/**
	 * Test written to test the output of the client into the console (this works partially
	 * as the play command is not issued properly) and to check whether the game flow works 
	 * as intended. Giving the player certain tiles and seeing whether he places them in valid
	 * places on the board. 
	 */
	@Test
	void testPlayTurn() {
		testInit();
		try {
			chin = new BufferedReader(new InputStreamReader(s.getInputStream()));
			chout = new BufferedWriter(new OutputStreamWriter(s.getOutputStream()));
			Board b = new Board();
			
			sendMessage(Protocol.WAITING + " " + 1);
			sendMessage(Protocol.ENTERED + clientA.getClientName());
			sendMessage(Protocol.WAITING + " " + 2);
			sendMessage(Protocol.ENTERED + " anotherPlayer");
			sendMessage(Protocol.START + " " + clientA.getClientName() + " anotherPlayer");
			sendMessage(Protocol.TILESUPDATE + " " + clientA.getClientName() + " WWW1");
			sendMessage(Protocol.TILESUPDATE + " anotherPlayer RRR6");
			sendMessage(Protocol.YOURTURN + " " + clientA.getClientName());
			String resp = chin.readLine();
			Move move = parsePlaceMove(resp);
			assertNotNull(move);
			List<Integer> coord = Board.index2Coord(move.getIndex());
			int row = coord.get(0);
			int column = coord.get(1);
			sendMessage(Protocol.PLACEUPDATE + " " + clientA.getClientName() + " " + 
					move.getTile().toString() + " " + row + " " + column + " " + 
					move.getTile().getRotation().toString());
			move.getTile().applyVariant(move.getVariant());
			b.setField(move.getIndex(), move.getTile());
			sendMessage(Protocol.TILESUPDATE + " " + clientA.getClientName() + " GGG6");
			sendMessage(Protocol.YOURTURN + " " + clientA.getClientName());
			resp = chin.readLine();
			move = parsePlaceMove(resp);
			move.getTile().applyVariant(move.getVariant());
			try {
				assertTrue(b.isValidMove(move.getIndex(), move.getTile()));
			} catch (InvalidIndexException e) {
				// not happening
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
    	
		
	}
	
	@AfterEach
	void tearDown() {
		try {
			server.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	@After
	void exit() {
		System.exit(0);
	}

	public Move parsePlaceMove(String resp) {
		Move move = null;
		try (Scanner sc = new Scanner(resp)) {
			if (sc.hasNext()) {
				Board board = new Board();
				String command = sc.next();
				assertTrue(command.equals(Protocol.PLACE));
				String tile = sc.next();
				int row = sc.nextInt();
				int column = sc.nextInt();
				int index = Board.coord2Index(row, column);
				assertTrue(index >= 0 && index < 36);
				assertTrue(tile.equals("WWW1") && 
						!board.getField(index).isBonus() || tile.equals("GGG6"));
				String rot = sc.next();
				assertTrue(Rotation.getRotations().contains(rot));
				RotatableTile rt = new RotatableTile(tile);
				boolean ud = board.getField(index).isUpsideDown();
				move = new Move(MoveType.PLACE, index, rt, rt.getVariant(ud ? "U" + rot : rot));
				return move;
			}
		}
		return null;
	}
	
	public void sendMessage(String msg) {
		try {
			chout.write(msg);
			chout.newLine();
			chout.flush();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	
}
