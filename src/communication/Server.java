package communication;

import controller.MarionettePlayer;
import model.Player;
import model.RotatableTile;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.BindException;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * Server class for use in Spectrangle game. 
 * @author  Corjan van den Brink (based on code template from Theo Ruys)
 * @author	Arne de Roode
 * @version 2019.01.30
 */
public class Server extends Thread implements Protocol {
	
    // Starts server
    public static void main(String[] args) {
		print("Welcome to the Spectrangle server, please fill in the following details"
				+ " to start the server");

    	int port = 0;

    	boolean validServerStarted = false;

    	while (!validServerStarted) {
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

			/*
			 * try to create a server on the given port, if not available a bind exception
			 * will be thrown which is caught and corresponding error will be printed.
			 */
			
			try {
				// create server
				Server server = new Server(port);
				server.run();
				validServerStarted = true;
			} finally {
				System.exit(0);
			}
		}

    }

    private int port;
    private List<ClientHandler> threads;
    
    // update this variable with extra features if implemented
    public static String[] serverFeatures = {};
    
    private List<Room> rooms;
    public InetAddress host = null;
    private boolean closed = false;
    
    /**
     * Constructs a new Server object.
     * @param portArg port on which server will run
     */
    public Server(int portArg) {
        port = portArg;
        threads = new ArrayList<>();
        rooms = new ArrayList<>();
    }
    
    /**
     * Listens to a port of this Server if there are any Clients that 
     * would like to connect. For every new socket connection a new
     * ClientHandler thread is started that takes care of the further
     * communication with the Client.
     */
    public void run() {
    	try (ServerSocket server = new ServerSocket(port)) {
            print("Server started, waiting for connections.");
            while (!closed) {
				Socket s = server.accept();
				ClientHandler ch = new ClientHandler(this, s);
				ch.features();
				ch.start();
				addHandler(ch);
            }
		} catch (BindException e) {
			print("ERROR: port " + port + " not available");
    	} catch (IOException e) {
			e.printStackTrace();
		} catch (IllegalArgumentException e) {
			print("ERROR: portnumber out of range");
		} finally {
			System.exit(0);
		}
    }
    
    /**
	 * Prints message to UI.
	 * @param msg Message to be displayed
	 */
    public static void print(String msg) {
        System.out.println(msg);
    }
    
    /**
     * Sends a message using the collection of connected ClientHandlers
     * to all connected Clients.
     * @param msg Message that is send
     */
    public void broadcast(String msg) {
        for (ClientHandler ch: threads) {
        	ch.sendMessage(msg);
        }
    }
    
    /**
     * Adds a ClientHandler to the collection of ClientHandlers.
     * @param handler ClientHandler that will be added
     */
    public void addHandler(ClientHandler handler) {
        threads.add(handler);
        print("New client connected. "
				+ "Total connections: " + threads.size());
    }
    
    /**
     * Removes a ClientHandler from the collection of ClientHandlers. 
     * @param handler ClientHandler that will be removed
     */
    public void removeHandler(ClientHandler handler) {
		Iterator<Room> roomIt = rooms.iterator();
        while (roomIt.hasNext()) {
        	Room r = roomIt.next();
        	if (r.hasClient(handler) && r.isStarted()) {
        		r.remove(handler);
        		for (ClientHandler remaining: r.getClients()) {
        			remaining.sendMessage(DISCONNECTED + " " + handler.getClientName());
        			
        			if (r.getClients().size() < r.getSize() - 1) {
        				removeHandler(remaining);
        			} else {
        				String endMessage = END;
            			for (Player p: r.getPlayers()) {
            				endMessage = endMessage.concat(" " + p.getName() + " " + p.getPoints());
            			}
            			remaining.sendMessage(endMessage);
        			}
        		}
        		roomIt.remove();
        	} else if (r.hasClient(handler)) {
        		r.remove(handler);
        		for (ClientHandler remaining: r.getClients()) {
        			remaining.sendMessage(DISCONNECTED + " " + handler.getClientName());
        		}
        	}
        }
    	threads.remove(handler);
        print("Connection closed.");
    }
    
    //-----
    
    /**
     * Returns the implemented server features.
     * @return server features
     */
    public String[] getServerFeatures() {
    	return serverFeatures;
    }
    
    /**
     * Adds ClientHandler to room. Checks if non-full suitable room exists and otherwise
     * adds new room for this player. Also takes care of communication to player and others
     * in room.
     * @param ch ClientHandler to be added
     * @param roomSize Requested room size
	 * @return Room room that ClientHandler was added to
     */
    public Room addToRoom(ClientHandler ch, int roomSize) {
    	for (Room r: rooms) {
    		if (r.getSize() == roomSize && !r.isFull()) {
    			List<ClientHandler> clients = r.getClients();
    			if (!r.join(ch)) {
    				ch.sendMessage(USERNAMETAKEN);
    				return null;
    			}

    			for (ClientHandler p: clients) {
					p.sendMessage(WAITING + " " + (clients.size()));
    				p.sendMessage(ENTERED + " " + ch.getClientName());

    			}
    			// start game if room is full
    			if (r.isFull()) {
    				List<Player> players = new ArrayList<>();
    				String names = "";
    				for (ClientHandler client : r.getClients()) {
    					String name = client.getClientName();
    					names = names + " " + name;
    					players.add(new MarionettePlayer(name));
					}
    				for (ClientHandler client: r.getClients()) {
    					client.sendMessage(START + names);
    				}
					startRoom(r, players);
    			}
    			return r;
    		}
    	}
    	Room newRoom = new Room(roomSize);
    	List<ClientHandler> players = newRoom.getClients();
		if (!newRoom.join(ch)) {
			ch.sendMessage(USERNAMETAKEN);
			return null;
		}

		for (ClientHandler p : players) {
			p.sendMessage(WAITING + " " + (players.size()));
			p.sendMessage(ENTERED + " " + p.getClientName());

		}
		rooms.add(newRoom);
		return newRoom;
    }

    /**
     * Starts a room with players. Responsible for dealing all tiles and giving the
     * first turn to a player.
     * @param room full room that will start a game
     * @param players players in this game
     */
    public void startRoom(Room room, List<Player> players) {
    	room.start(players); // deal tiles
    	
    	//let clients know all tiles of all players
		Iterator<Player> playerIt = room.getGame().getPlayers().iterator();
		while (playerIt.hasNext()) {
			Player currentPlayer = playerIt.next();
			String playerName = currentPlayer.getName();
			List<RotatableTile> playerTiles = currentPlayer.getTiles();

			String playerTilesString = "";
			for (RotatableTile tile : playerTiles) {
				playerTilesString = playerTilesString.concat(" " + tile.toString());
			}

			for (ClientHandler ch : room.getClients()) {
				ch.sendMessage(TILESUPDATE + " " + playerName + playerTilesString);
			}
		}

		ClientHandler currentClient = room.getClients().get(0);
		currentClient.sendMessage(YOURTURN + " " + currentClient.getClientName());
	}
    
    /**
     * ends a room, emptying it and removing it from the server.
     * @param room room with ended game
     */
    public void endRoom(Room room) {
    	while (!room.getClients().isEmpty()) {
    		room.remove(room.getClients().get(0));
		}
		rooms.remove(room);
    }
    
    /**
     * Closes the server, only called if from outside the value for closed is set true.
     */
    public void closeServer() {
    	print("Closing server...");
    	closed = true;
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

}
