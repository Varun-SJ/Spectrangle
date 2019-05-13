package communication;

import controller.ComputerPlayer;
import controller.Game;
import controller.HumanPlayer;
import controller.MarionettePlayer;
import model.*;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.net.SocketException;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

/**
 * Client class for use in Spectrangle game.
 * @author  Corjan van den Brink (based on code template from Theo Ruys)
 * @author	Arne de Roode
 * @version 2019.01.30
 */
public class Client extends Thread implements Protocol {

	// Starts client
	public static void main(String[] args) {
		InetAddress host = null;
		int port = 0;

		print("Welcome to the Spectrangle client, please fill in the following "
				+ "details to connect to s server and start a game");

		// get and check host
		boolean validHost = false;
		while (!validHost) {
			String address = readString("Host address: ");
			try {
				host = InetAddress.getByName(address);
				validHost = true;
			} catch (UnknownHostException e) {
				print("ERROR: invalid hostname");
			}
		}

		// get and check port
		boolean validPort = false;
		while (!validPort) {
			try {
				port = Integer.parseInt(readString("Host port: "));
				if (port >= 0) {
					validPort = true;
				} else {
					print("ERROR: invalid portnumber");
				}
			} catch (NumberFormatException e) {
				print("ERROR: invalid portnumber");
			}
		}

		// query the user for name
		String playerName = "";
		String playerType = "";

		boolean validName = false;
		while (!validName) {
			playerName = readString("Player name: ");
			if (playerName.length() > 0) {
				validName = true;
			} else {
				print("ERROR: invalid player name");
			}
		}

		// query the user for type of player
		boolean validType = false;
		print("Choose the type of player. (Options: human, computer-naive)");
		while (!validType) {
			playerType = readString("Player type: ");
			playerType = playerType.toLowerCase();

			if (playerType.equals("human") || playerType.equals("computer-naive")) {
				validType = true;
			} else {
				print("ERROR: invalid player type");
			}
		}


		// create client instance
		try {
			Client client = new Client(host, port, playerName, playerType);
			// start listening
			client.start();
		} catch (IOException e) {
			print("ERROR: couldn't construct a client object, maybe the provided address "
					+ "or port were wrong");
			System.exit(0);
		}

	}

	private Socket sock;
	private BufferedReader in;
	private BufferedWriter out;

	private String clientName;
	private Strategy strategy;
	private Player thisPlayer;
	private Game game;
	
	// update this variable with extra features if implemented
	public static String[] clientFeatures = {};

	/**
	 * Constructs a Client-object and tries to make a socket connection.
	 * @param host Host address
	 * @param port Port number
	 * @param name name of user
	 * @param playerType for now human or computer-[strategyname]
	 * @throws IOException on failing to create the in/out streams
	 */
	public Client(InetAddress host, int port, String name, String playerType) throws IOException {
		sock = new Socket(host, port);
		in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
    	out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));


    	clientName = name;

    	switch (playerType) {
			case "human": {
				thisPlayer = new HumanPlayer(clientName);
				break;
			}
			case "computer-naive": {
				strategy = new NaiveStrategy();
				thisPlayer = new ComputerPlayer(clientName, strategy);
				break;
			}
		}
	}

	/**
	 * Reads the messages in the socket connection. Each message will
	 * be forwarded to the MessageUI
	 */
	public void run() {
		try {
    		String msg;
			while ((msg = in.readLine()) != null) {
//				System.out.println(msg);
				handleServerMessages(msg);
			}
		} catch (SocketException e) {
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			shutdown();
		}
	}
	
	/**
	 * Handles server commands.
	 * @param message Server command
	 */
	public void handleServerMessages(String message) {
		try (Scanner sc = new Scanner(message)) {
			if (sc.hasNext()) {
				String command = sc.next();

				switch (command) {
					case SERVERFEATURES: {
						print("Server supports features: ");
						String cfCommand = "client_features";
						for (String feature: clientFeatures) {
							print(feature);
							cfCommand = cfCommand.concat(" " + feature);
						}
						sendMessage(cfCommand);

						newStart("Play the game!");

						break;
					}
					case WAITING: {
						print("Currently " + Integer.parseInt(sc.next()) + " players waiting");
						break;
					}
					case ENTERED: {
						String name = sc.next();

						print(name + " entered the lobby");
						break;
					}
					case START: {
						// start game
						List<Player> playerList = new ArrayList<>();

						print("Game is starting");
						String players = "";

						String playerName;
						while (sc.hasNext()) {
						    playerName = sc.next();
							players = players.concat(" " + playerName);

							Player player;
							if (playerName.equals(clientName)) {
								player = thisPlayer;
                            } else {
							    player = new MarionettePlayer(playerName);
                            }

                            playerList.add(player);
						}
						print("Players: " + players);

						this.game = new Game(playerList);

						break;
					}
					case YOURTURN: {
						// if my turn: determine move and send to server
                        String current = sc.next();
                        if (current.equals(clientName)) {
                            // it is my turn
                            Move move = thisPlayer.determineMove(this.game.getBoard());
                            String serverCommandString = "";
                            switch (move.getType()) {
								case PLACE: {
									move.getTile().applyVariant(move.getVariant());

                                    List<Integer> coords = Board.index2Coord(move.getIndex());
                                    int row = coords.get(0);
                                    int column = coords.get(1);

									serverCommandString = move.getType().toString().toLowerCase() + 
											" " + move.getTile().toString() + " " + row + " " + 
											column + " " + move.getTile().getRotation().toString();
									break;
								}
								case DISCARD: {
									serverCommandString = move.getType().toString().toLowerCase() +
											" " + move.getTile().toString();
									break;
								}
								case PASS: {
									serverCommandString = move.getType().toString().toLowerCase();
									break;
								}
							}
							System.out.println(serverCommandString);

                            sendMessage(serverCommandString);
                        } else {
                            // else print whose turn it is
                            print("Current player's turn: " + current);
                        }
                        break;
					}
					case PLACEUPDATE: {
						// update my local game version according to data provided
                        sc.next(); // skip player name
                        String tileString = sc.next();
                        int row = Integer.parseInt(sc.next());
                        int column = Integer.parseInt(sc.next());
                        String orientation = sc.next();

                        boolean isUpsideDown = (row + column) % 2 == 1;

                        RotatableTile tile =  new RotatableTile(tileString);

                        String key = "";
                        if (isUpsideDown) {
                            key = key.concat("U");
                        }
                        key = key.concat(orientation);

                        Move move = new Move(MoveType.PLACE, 
                        		Board.coord2Index(row, column), tile, tile.getVariant(key));

                        game.doMove(move);
                        // print game board

						game.update();

                        break;
					}
                    case TILESUPDATE: {
                        String playerName = sc.next();
                        List<RotatableTile> tiles = new ArrayList<>();

                        String printString = "Player : " + playerName + " currently has tiles: ";

                        // read the tiles of the current player into the tiles list
                        while (sc.hasNext()) {
                            String tileString = sc.next();
                            RotatableTile tile = new RotatableTile(tileString);
                            tiles.add(tile);
							printString = printString.concat(tileString + " ");
                        }

                        // resync this player's tiles
                        for (Player p : game.getPlayers()) {
                            if (p.getName().equals(playerName)) {
                                p.removeTiles();
                                for (RotatableTile tile : tiles) {
                                    p.addTile(tile);
                                }
                            }
                        }

                        print(printString);

                        game.nextPlayer();
                        break;
                    }
					case DISCONNECTED: {
						// in case someone disconnects, say who has disconnected
                        print("Player disconnected: " + sc.next());
                        break;
					}
                    case END: {
                        // End the game, print the scores
						while (sc.hasNext()) {
							String printString = " " + sc.next() + ": " + 
									Integer.parseInt(sc.next());
							print(printString);
						}
						game = null;
						newStart("Do you want to play another game? ");
                        break;
                    }
                    case ERROR: {
                        // print error
						int errno = Integer.parseInt(sc.next());
						String printString = "ERROR: " + sc.next() + " (" + errno + ")";
						print(printString);
						if (game == null) {
						    newStart("Error in trying to play a new game. Try to 'play' again..");
                        }
						break;
                    }
				}
			}
			return;
		}
	}

	/**
	 * Method responsable for the UI part and for replayability.
	 * @param startMessage message to print the query with for a play command
	 */
	private void newStart(String startMessage) {
		print("\n" + startMessage);
		String playString = readString("If you want to play, type: "
				+ "play <#players (2-4)>, otherwise type: exit");

		String[] words = playString.split(" ");
		if (words[0].equals("play") && words.length == 2) {
            sendMessage(playString + " " + clientName);
        } else if (words[0].equals("quit")) {
        	try {
				sock.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
        	System.exit(0);
        } else {
		    newStart("Error: Invalid play command");
        }
	}

	//----- Standard methods -----

	/**
	 * Close the socket connection. Only on server disconnect.
	 */
	public void shutdown() {
		// server is dead
		print("ERROR: Server is not responding.");
		print("Closing socket connection...");
		try {
			sock.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		System.exit(0);
	}

	/** 
	 * Send a message to a ClientHandler.
	 * @param msg Message to ClientHandler (out)
	 */
	public void sendMessage(String msg) {
   		try {
			out.write(msg);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			shutdown();
		}
	}

	/**
	 * Prints message to UI.
	 * @param message Message to be displayed
	 */
	private static void print(String message) {
		System.out.println(message);
	}
	
	/**
	 * Reads line from the user input of the UI.
	 * @param text Query to the user
	 * @return User input string
	 */
	public static String readString(String text) {
		System.out.print(text);
		String resp = null;
		try {
			BufferedReader in = new BufferedReader(new InputStreamReader(
					System.in));
			resp = in.readLine();
		} catch (IOException e) {
		}
		return (resp == null) ? "" : resp;
	}

	/**
	 * Returns client name.
	 * @return this.clientName
	 */
	public String getClientName() {
		return clientName;
	}

	/**
	 * Returns clientFeatures.
	 * @return clientFeatures
	 */
	public String[] getClientFeatures() {
		return clientFeatures;
	}
}
