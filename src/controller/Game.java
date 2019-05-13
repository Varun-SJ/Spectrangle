package controller;

import java.util.ArrayList;
import java.util.List;

import model.Board;
import model.Field;
import model.Move;
import model.Player;
import model.RotatableTile;
import model.TilesBag;
import view.SpectrangleBoardPrinter;

/**
 * Class for controlling a Spectrangle game.
 * @author Corjan van den Brink
 * @version 2019.01.30
 */
public class Game {
	
	private List<Player> players;
	private Board board;
	private TilesBag tilesBag;
	private int currentPlayer = 0;
	private int consecutivePasses = 0;
	
	/**
	 * running this creates a human and a computerplayer to play against each other
	 * for testing purposes.
	 * @param args not necessary
	 */
	public static void main(String[] args) {
		List<Player> players = new ArrayList<>();
		players.add(new HumanPlayer("Corjan"));
		players.add(new ComputerPlayer("Levi"));
		
		Game game = new Game(players);
		game.setUpGame();
		game.play();
	}
	
	//@ invariant 0 < getCurrentPlayer() & getCurrentPlayer() < getClients().size();
	/**
	 * Constructor for game receives players list in a randomized order and sets up the
	 * the game for these players.
	 * @param players List of Players in their playing order
	 */
	public Game(List<Player> players) {
		this.players = players;
		this.tilesBag = new TilesBag();
		this.board = new Board();
	}

	
	/**
	 * Deals 4 tiles to each player.
	 */
	public void setUpGame() {
		for (Player p: getPlayers()) {
			for (int i = 0; i < 4; i++) {
				p.addTile(tilesBag.takeRandomTile());
			}
		}
	}
	
	/**
	 * Give the turn to the next player while the game is active and handle end of game.
	 */
	public void play() {
		// give players copy of board to prevent changing game state
		firstTurn();
		while (!isFinished()) {
			Move m = players.get(nextPlayer()).determineMove(getBoard());
			doMove(m);
			update();
		}
		
	}
	
	/**
	 * Give first turn to first player.
	 */
	private void firstTurn() {
		update();
		// give turn to first player
		Move m = players.get(0).determineMove(getBoard());
		doMove(m);
		update();
	}

	/**
	 * updates the UI for the game status.
	 */
	public void update() {
		List<Integer> values = new ArrayList<>();
		List<Character> right = new ArrayList<>(), left = new ArrayList<>(),
				other = new ArrayList<>();
		
		for (Field f: board.getFields()) {
			if (f.hasTile()) {
				values.add(f.getTile().getTilePoints());
				right.add(f.getTile().getVariant().getRightSide().toString().charAt(0));
				left.add(f.getTile().getVariant().getLeftSide().toString().charAt(0));
				other.add(f.getTile().getVariant().getOtherSide().toString().charAt(0));
			} else {
				values.add(null);
				right.add(null);
				left.add(null);
				other.add(null);
			}
			
		}
		
        System.out.println("Current game situation: \n" + 
        		SpectrangleBoardPrinter.getBoardString(values, other, left, right));
        String scoreboard = "";
        for (Player p: getPlayers()) {
        	scoreboard = scoreboard.concat(p.getName() + ": " + p.getPoints() + " points | ");
        }
        System.out.println(scoreboard + "\n");
    }
	
	/**
	 * check if game is finished.
	 * @return true if no one can make a turn or board is full
	 */
	public boolean isFinished() {
		if (tilesBag.isEmpty() && allPlayersPassed()) {
			return true;
		} else if (board.isFullBoard()) {
			return true;
		}
		
		return false;
	}
	
	/**
	 * if the amount of consecutive passes is all players, all have passed.
	 * @return true if all players passed
	 */
	public boolean allPlayersPassed() {
		return consecutivePasses == getPlayers().size();
	}

	/**
	 * Calculates the index of the next player and returns it.
	 * @return index for the next player
	 */
	public int nextPlayer() {
		currentPlayer = ++currentPlayer % players.size();
		return currentPlayer;
	}
	
	// ========= GamePlay =========
	
	/**
	 * Should update the board with a valid move.
	 * This can be an update to the fields, a discard of a tile or a pass.
	 * @param move the game board
	 */
	public void doMove(Move move) {		
		RotatableTile tile = move.getTile();
		switch (move.getType()) {
			case PLACE:
				tile.applyVariant(move.getVariant());
				placeTile(move.getIndex(), tile);
				getBoard().unEmptyBoard();
				break;
			case DISCARD:
				if (!getTileBag().isEmpty()) {
					discard(tile);
				} else {
					pass();
				}
				break;
			case PASS:
				pass();
				break;
			default:
				break;
		}
		
	}
	
	/*@
	 	requires getBoard().isValidMove(index, tile);
	 	ensures getBoard().getField(index).getTile().equals(tile) &
	 			getClients().get(getCurrentPlayer()).getPoints() ==
	 			\old(getClients().get(getCurrentPlayer()).getPoints()) +
	 			tile.getTilePoints() * getBoard().matchingSides(index, tile) * 
				getBoard().getField(index).getMultiplier();
	 */
	/**
	 * Makes the move by placing the tile and adding points.
	 * @param index index of field
	 * @param tile tile to be placed in right orientation
	 */
	public void placeTile(int index, RotatableTile tile) {
		consecutivePasses = 0;
		Field field = getBoard().setField(index, tile);
		Player current = getPlayers().get(getCurrentPlayer());
		current.addPoints(tile.getTilePoints() * 
				Math.max(1, getBoard().matchingSides(field.getIndex(), tile)) * 
				field.getMultiplier());
		current.removeTile(tile);
		if (!getTileBag().isEmpty()) {
			current.addTile(getTileBag().takeRandomTile());
		}
	}
	
	/**
	 * Discards a tile of the players set.
	 * @param tile tile from player
	 */
	public void discard(RotatableTile tile) {
		consecutivePasses = 0;
		Player current = getPlayers().get(getCurrentPlayer());
		current.removeTile(tile);
		current.addTile(getTileBag().takeRandomTile());
		getTileBag().addTile(tile);
	}
	
	/**
	 * Increment consecutive passes counter, other moves reset this counter.
	 * Used to keep track of end of game
	 */
	public void pass() {
		consecutivePasses++;
	}
	
	// ========== Getters ============
	
	/**
	 * Getter for board.
	 * @return board
	 */
	/*@ pure */ public Board getBoard() {
		return board;
	}
	
	/**
	 * Returns players (in their order).
	 * @return list of players
	 */
	/*@ pure */ public List<Player> getPlayers() {
		return players;
	}
	
	/**
	 * Gets current player index.
	 * @return index for currentPlayer from players list
	 */
	/*@ pure */ public int getCurrentPlayer() {
		return currentPlayer;
	}
	
	/**
	 * Gets the current tile bag.
	 * @return tileBag
	 */
	/*@ pure */ public TilesBag getTileBag() {
		return tilesBag;
	}
	
}
