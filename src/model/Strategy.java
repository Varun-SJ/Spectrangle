package model;

import java.util.List;

/**
 * Defines a strategy base interface for the computer player to implement.
 * @author Varun Sudhakar
 * @author Corjan van den Brink
 * @version 2019.01.28
 */
public interface Strategy {

	/**
	 * Determines the move according to this strategy.
	 * @param tiles the player's tiles
	 * @param board the current board (a copy thereof)
	 * @return valid move
	 */
	public Move determineMove(List<RotatableTile> tiles, Board board);

	/**
	 * Getter for name of the strategy.
	 * @return name
	 */
	public String getName();
}
