package controller;

import model.Board;
import model.Move;
import model.NaiveStrategy;
import model.Player;
import model.Strategy;

/**
 * Computer player class for playing the game according to a strategy.
 * @author Corjan van den Brink
 * @version 2019.01.28
 */
public class ComputerPlayer extends Player {
	
	private Strategy strategy;

	/**
	 * Creates CP with (four) tiles and strategy.
	 * @param name name of this CP
	 * @param strategy strat for this CP
	 */
	public ComputerPlayer(String name, Strategy strategy) {
		super(name);
		this.strategy = strategy;
	}
	
	/**
	 * Default constructor for NaiveStrategy PC player.
	 * @param name name for CP
	 */
	public ComputerPlayer(String name) {
		this(name, new NaiveStrategy());
		
	}

	@Override
	/**
	 * Determines move for the computer player.
	 */
	public Move determineMove(Board board) {
		return getStrategy().determineMove(getTiles(), board);
	}

	/**
	 * Getter for strategy.
	 * @return strategy strat for this CP
	 */
	public Strategy getStrategy() {
		return strategy;
	}

}
