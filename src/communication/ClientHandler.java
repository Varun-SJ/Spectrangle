package communication;

import controller.InvalidIndexException;
import controller.InvalidMoveException;
import model.*;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.net.SocketException;
import java.util.*;

/**
 * ClientHandler class for use in Spectrangle game.
 * @author	Corjan van den Brink (based on code template from Theo Ruys)
 * @author	Arne de Roode
 * @version 2019.01.30
 */
public class ClientHandler extends Thread implements Protocol {
    
	private Server server;
    private BufferedReader in;
    private BufferedWriter out;
    private String clientName = "";
	List<String> commonFeatures = new ArrayList<>();
	
	public boolean inRoom = false;
	private boolean isStarted = false;
	private Room room = null;

    /**
     * Constructs a ClientHandler object and
     * initializes both Data streams.
     * @param serverArg The server for the ClientHandler
     * @param sockArg Server's connection socket to the client
     * @throws IOException on failing to create the in/out streams
     */
    //@ requires serverArg != null && sockArg != null;
    public ClientHandler(Server serverArg, Socket sockArg) throws IOException {
        server = serverArg;
        in = new BufferedReader(new InputStreamReader(sockArg.getInputStream()));
    	out = new BufferedWriter(new OutputStreamWriter(sockArg.getOutputStream()));
    }
    
    /**
     * Method for handling the sending and receiving of features at 
     * the initialization of the Server Client connection.
     */
    public void features() {
    	//send server features
    	String sfCommand = SERVERFEATURES;
    	String[] serverFeatures = server.getServerFeatures();
    	for (String feature: serverFeatures) {
    		sfCommand = sfCommand.concat(" " + feature);
    	}
    	sendMessage(sfCommand);
    	
    	//get client features
    	String cfCommand = null;
    	try {
    		while (cfCommand == null) {
    			cfCommand = in.readLine();
    		}
		} catch (IOException e) {
			e.printStackTrace();
		}
    	
    	//get common features and let server know
    	try (Scanner sc = new Scanner(cfCommand);) {
			if (sc.hasNext() && sc.next().equals(CLIENTFEATURES)) {
				while (sc.hasNext()) {
					String clientFeature = sc.next();
					for (String serverFeature: serverFeatures) {
						if (clientFeature.equals(serverFeature)) {
							commonFeatures.add(clientFeature);
						}
					}
				}
			} else {
				sendMessage(INVALIDCOMMAND);
			}
    	}
    }

    /**
     * This method takes care of sending messages from the Client.
     * Every message that is received, is handled here.
     * If a client is not responding, the method concludes that 
     * the socket connection is broken and shutdown() will be called. 
     */
    public void run() {
    	try {
    		String msg;
			while ((msg = in.readLine()) != null) {
				handleClientServer(msg);
			}
		} catch (SocketException e) {
    		// client dies, shutdown thread
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			shutdown();
		}
    }

    /**
     * Handles Client to Server communication.
     * Intercepts C>S messages and calls appropriate methods while catching errors or
     * false messages.
     * @param msg C>S message
     */
    private void handleClientServer(String msg) {
    	printMessageExchange(msg, 'c');
		try (Scanner sc = new Scanner(msg)) {
			if (sc.hasNext()) {
				String command = sc.next();
				switch (command) {
					case PLAY : {
						if (!inRoom) {
							int gameSize = sc.nextInt();
							if (gameSize < 2 || gameSize > 4) {
								sendMessage(INVALIDPARAMETERS);
								break;
							}
							clientName = sc.next();
							Room r = server.addToRoom(this, gameSize);
							if (r != null) {
								this.inRoom = true;
								this.room = r;
								this.isStarted = this.room.isStarted();
							}
						} else {
							sendMessage(INVALIDCOMMAND);
						}
						break;
					}
					case PLACE: {
						if (!inRoom || !isStarted()) {
							sendMessage(INVALIDCOMMAND);
						} else if (!isMyTurn()) {
							sendMessage(NOTYOURTURN);
						} else {
							String broadCastString = PLACEUPDATE + " " + getClientName() + " ";
							
							// parse command
							String tileString = sc.next();
							int row = Integer.parseInt(sc.next());
							int column = Integer.parseInt(sc.next());
							String orientation = sc.next();

							boolean isUpsideDown = (row + column) % 2 == 1;
							
							// check parameters
							if (row < 0 || row > 5 || column > row || column < -row ||
									orientation.length() > 1 ||
									!Rotation.getRotations().contains(orientation) ||
									tileString.length() != 4) {
								sendMessage(INVALIDPARAMETERS);
								break;
							}

							try {
								Player player = getRoom().getGame()
										.getPlayers().get(getRoom().getGame().getCurrentPlayer());
								RotatableTile tile = player.findTileByString(tileString);

								if (tile == null) {
									throw new InvalidMoveException(MoveType.PLACE);
								}

								String key = "";
								if (isUpsideDown) {
									key = key.concat("U");
								}
								key = key.concat(orientation);

								// create move
								Move move = new Move(MoveType.PLACE, 
										Board.coord2Index(row, column), tile, tile.getVariant(key));
								
								// validate move
                                validateMove(getRoom().getGame().getBoard(), move, player);
                                
								// do move on game
								getRoom().getGame().doMove(move);

								broadCastString = broadCastString.concat(tileString + " " + row
										+ " " + column + " " + orientation);
								getRoom().broadcast(broadCastString);

								sendTilesUpdate();

								if (!checkGameFinished()) {
									getRoom().broadcast(YOURTURN + " " + getRoom().getGame()
										.getPlayers().get(
											getRoom().getGame().getCurrentPlayer()).getName());
								}
							} catch (InvalidMoveException e) {
								sendMessage(INVALIDMOVE);
							}
						}
						break;
					}
					case DISCARD: {
						if (!inRoom || !isStarted()) {
							sendMessage(INVALIDCOMMAND);
						} else if (!isMyTurn()) {
							sendMessage(NOTYOURTURN);
						} else {
							String tileString = sc.next();


							try {
                                Player player = getRoom().getGame().getPlayers().get(
                                		getRoom().getGame().getCurrentPlayer());
                                RotatableTile tile = player.findTileByString(tileString);

                                Move move = new Move(MoveType.DISCARD, tile);
								validateMove(getRoom().getGame().getBoard(), move, player);

								getRoom().getGame().doMove(move);

								sendTilesUpdate();

								if (!checkGameFinished()) {
									getRoom().broadcast(YOURTURN + " " + getRoom().getGame()
										.getPlayers().get(
											getRoom().getGame().getCurrentPlayer()).getName());
								}

							} catch (InvalidMoveException e) {
								sendMessage(INVALIDMOVE);
							}
						}
						break;
					}
					case PASS: {
						if (!inRoom || !isStarted()) {
							sendMessage(INVALIDCOMMAND);
						} else if (!isMyTurn()) {
							sendMessage(NOTYOURTURN);
						} else {

							try {
								Move move = new Move(MoveType.PASS);
								Player player = getRoom().getGame().getPlayers()
									.get(getRoom().getGame().getCurrentPlayer());

								validateMove(getRoom().getGame().getBoard(), move, player);

								getRoom().getGame().doMove(move);

								sendTilesUpdate();

								if (!checkGameFinished()) {
									getRoom().broadcast(YOURTURN + " " + getRoom().getGame()
										.getPlayers().get(
											getRoom().getGame().getCurrentPlayer())
											.getName());
								}
							} catch (InvalidMoveException e) {
								sendMessage(INVALIDMOVE);
							}
						}
						break;
					}
					case CLIENTFEATURES:
						sendMessage(INVALIDCOMMAND);
						break;
					default:
						sendMessage(UNKNOWNCOMMAND);
				}

			}
		} catch (InputMismatchException e) {
			sendMessage(INVALIDCOMMAND);
		} catch (NoSuchElementException e) {
			sendMessage(INVALIDPARAMETERS);
		}
    	
	}

    /**
     * Method for validating a Move instance to check whether the client provided a valid move.
     * @param board game board
     * @param move client's move
     * @param player player making the move
     * @throws InvalidMoveException if move in invalid, to be caught and for sending back an error.
     */
	private void validateMove(Board board, Move move, Player player) throws InvalidMoveException {

		switch (move.getType()) {
			case PLACE: {
			    // check if player has the tile
                RotatableTile tile = move.getTile();
                if (!player.getTiles().contains(tile)) {
                    throw new InvalidMoveException(MoveType.PLACE);
                }
				tile.applyVariant(move.getVariant());

				// check if move is valid on the board
				try {
					board.isValidMove(move.getIndex(), tile);
				} catch (InvalidIndexException e) {
					throw new InvalidMoveException(MoveType.PLACE);
				}
				break;
			}
			case DISCARD: {
                // check if player has the tile
                RotatableTile tile = move.getTile();
                if (!player.getTiles().contains(tile)) {
                    throw new InvalidMoveException(MoveType.DISCARD);
                }
                
				// check if no available move, if move available: must move
				NaiveStrategy moveFindingStrategy = new NaiveStrategy();
				List<Move> availableMoves = moveFindingStrategy
						.findPlaceMoves(player.getTiles(), board);
				if (!availableMoves.isEmpty()) {
					throw new InvalidMoveException(MoveType.DISCARD);
				}
				break;
			}
			case PASS: {
				//check if no available move
				NaiveStrategy moveFindingStrategy = new NaiveStrategy();
				List<Move> availableMoves = moveFindingStrategy
						.findPlaceMoves(player.getTiles(), board);
				if (!availableMoves.isEmpty()) {
					throw new InvalidMoveException(MoveType.PASS);
				}
				break;
			}
		}


	}

	/**
	 * Method that based on the current player will send everyone the new tiles for this player.
	 * Is called after a turn is validated server side.
	 */
	private void sendTilesUpdate() {
		Player player = getRoom().getGame()
				.getPlayers().get(getRoom().getGame().getCurrentPlayer());

		String broadcastString = TILESUPDATE + " " + getClientName();
		for (RotatableTile tile : player.getTiles()) {
			broadcastString = broadcastString.concat(" " + tile.toString());
		}
		
		getRoom().getGame().nextPlayer();
		getRoom().broadcast(broadcastString);
	}

	/**
	 * Method for handling the end of the game.
	 * @return true if game is finished
	 */
	private boolean checkGameFinished() {
    	boolean isFinished = getRoom().getGame().isFinished();

    	if (isFinished) {
    		String endMessage = END;
			for (Player p: getRoom().getPlayers()) {
				endMessage = endMessage.concat(" " + p.getName() + " " + p.getPoints());
			}
			getRoom().broadcast(endMessage);
			server.endRoom(getRoom());
		}
		return isFinished;
	}

	/**
	 * This ClientHandler signs off from the Server. 
	 */
	private void shutdown() {
	    server.removeHandler(this);
	}

	/**
     * This method can be used to send a message over the socket
     * connection to the Client. If the writing of a message fails,
     * the method concludes that the socket connection has been lost
     * and shutdown() is called.
     * @param msg message to send to client
     */
    public void sendMessage(String msg) {
    	printMessageExchange(msg, 's');
        try {
			out.write(msg);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			shutdown();
		}
    }

    /**
     * part of UI for showing all communication plus the direction.
     * @param msg message that is sent
     * @param src s or c as source for showing correct direction of messages
     */
    private void printMessageExchange(String msg, char src) {
    	String exchange = "";
    	switch (src) {
			case 'c': {
				// message from client to server
				exchange = "Client -> Server : " + msg;
				break;
			}
			case 's': {
				// message from client to server
				exchange = "Server -> Client : " + msg;
				break;
			}
		}
		System.out.println(exchange);
	}

    /**
     * Check if the turn is for the player that this client handler is responsible for.
     * @return true if game returns current player is this client
     */
	private boolean isMyTurn() {
		if (getRoom().getGame().getPlayers().get(getRoom().getGame().getCurrentPlayer())
				.getName().equals(getClientName())) {
			return true;
		}
		return false;
	}

	/**
	 * Checks if game is started based on room status.
	 * @return true if game has been started
	 */
	private boolean isStarted() {
		if (getRoom() != null) {
			this.isStarted = getRoom().isStarted();
		} else {
			this.isStarted = false;
		}
		return this.isStarted;
	}

	/**
	 * Getter for room.
	 * @return room
	 */
	/*@ pure */ public Room getRoom() {
		return room;
	}

	/**
	 * Gets the name of the client (default this.toString()).
	 * @return useful and pretty unique or Client set string
	 */
	/*@ pure */ public String getClientName() {
		return clientName;
	}
}
