package communication;

import controller.Game;
import model.Player;

import java.util.ArrayList;
import java.util.List;

/**
 * Class for handling game rooms.
 * @author Corjan van den Brink
 * @author Arne de Roode
 * @version 2019.01.30
 */
public class Room {
	
	private List<ClientHandler> clients = new ArrayList<>();
	private int size;
	private boolean gameStarted;
	private Game game;
	
	/*@ invariant 2 <= getSize() & getSize() <= 4;
		invariant getClients().size() <= getSize();
		invariant isStarted() ==> isFull();
	 */
	
	//@ requires 2 <= size & size <= 4;
	public Room(int size) {
		this.size = size;
	}
	
	/*@
	 	requires !isFull() & player != null;
	 	ensures (\forall ClientHandler other; getClients().contains(other);
	 			!other.getClientName().equals(player.getClientName())) ==>
	 			getClients().contains(player);
	 */
	/**
	 * Try to join a client to the room.
	 * @param client ClientHandler for the client
	 * @return false if there is a client with the same name already in the room
	 */
	public boolean join(ClientHandler client) {
		for (ClientHandler other: getClients()) {
			if (client.getClientName().equals(other.getClientName())) {
				return false;

			}
		}
		getClients().add(client);
		client.inRoom = true;
		return true;
	}
	
	/*@
	 	requires player != null;
	 	ensures !getClients().contains(player);
	 */
	/**
	 * Removes the client from the room.
	 * @param client ClientHandler for the client
	 */
	public void remove(ClientHandler client) {
		getClients().remove(client);
		client.inRoom = false;
	}
	
	/*@
	 	ensures (getSize() == getClients().size()) ==> \result;
	 	pure
	*/
	/**
	 * Checks if the room is occupied.
	 * @return true if size == clients.size()
	 */
	public boolean isFull() {
		return getSize() == getClients().size();
	}
	
	/**
	 * Getter for size.
	 * @return size
	 */
	/*@ pure */ public int getSize() {
		return size;
	}
	
	/**
	 * Getter for clients in the room.
	 * @return List of ClientHandlers in this room
	 */
	/*@ pure */ public List<ClientHandler> getClients() {
		return clients;
	}
	
	/**
	 * Checks if player is in this room.
	 * @param player ClientHandler the server looks for
	 * @return true if player is in this room
	 */
	public boolean hasClient(ClientHandler player) {
		return getClients().contains(player);
	}
	
	/**
	 * Returns if the game has started.
	 * @return true if game has been full
	 */
	/*@ pure */ public boolean isStarted() {
		return gameStarted;
	}
	
	/**
	 * Starts game.
	 * @param players list of players in order for constructing a game
	 */
	public void start(List<Player> players) {
		gameStarted = true;
		// set up game
		game = new Game(players);
		game.setUpGame();

	}

	/**
	 * Gets if game is started.
	 * @return true if gameStarted
	 */
	public boolean isGameStarted() {
		return gameStarted;
	}

	/**
	 * Gets game.
	 * @return game
	 */
	public Game getGame() {
		return game;
	}

	/**
	 * Gets a list of players in this room.
	 * @return players from the game
	 */
	public List<Player> getPlayers() {
		return this.game.getPlayers();
	}

	/**
	 * Broadcast a message to all clients in this room.
	 * @param msg message to the clients
	 */
	public void broadcast(String msg) {
		for (ClientHandler ch: getClients()) {
			ch.sendMessage(msg);
		}
	}

}
