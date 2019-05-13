package controller;

import model.Board;
import model.Move;
import model.Player;

/**
 * Marionette player is a class used by the server and the Client to keep track of players
 * from connected Clients. These basically have no behavior but are keeping track of points
 * and tiles for the Game to run smoothly.
 * @author Corjan van den Brink
 * @version 2019.01.29
 */
public class MarionettePlayer extends Player {

    public MarionettePlayer(String name) {
        super(name);
    }

    @Override
    public Move determineMove(Board board) {
        return null;
    }

}