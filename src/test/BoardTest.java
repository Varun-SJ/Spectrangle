package test;

import static org.junit.jupiter.api.Assertions.*;

import java.util.ArrayList;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import controller.InvalidIndexException;
import model.Board;
import model.Color;
import model.RotatableTile;

class BoardTest {
	private Board board;

	@BeforeEach
	void setUp() throws Exception {
		board = new Board();
	}

	@Test
	void testBoard() {

		assertEquals(1, board.getField(0).getMultiplier());
		assertEquals(1, board.getField(33).getMultiplier());
		assertEquals(1, board.getField(12).getMultiplier());

		assertEquals(2, board.getField(10).getMultiplier());
		assertEquals(2, board.getField(14).getMultiplier());
		assertEquals(2, board.getField(30).getMultiplier());

		assertEquals(3, board.getField(2).getMultiplier());
		assertEquals(3, board.getField(26).getMultiplier());
		assertEquals(3, board.getField(34).getMultiplier());

		assertEquals(4, board.getField(11).getMultiplier());
		assertEquals(4, board.getField(13).getMultiplier());
		assertEquals(4, board.getField(20).getMultiplier());
	}

	@Test
	void testIsValidIndex() {
		// Test for no negative indices
		assertFalse(board.isValidIndex(-2));

		for (int i = 0; i < Board.BOARD_SIZE; i++) {
			assertTrue(board.isValidIndex(i));
		}

		assertFalse(board.isValidIndex(Board.BOARD_SIZE));
		assertFalse(board.isValidIndex(Board.BOARD_SIZE + 5));
	}

	@Test
	void testIsValidMove() throws InvalidIndexException {
		RotatableTile tile1 = new RotatableTile(Color.B, Color.P, Color.G, 4);
		RotatableTile tile2 = new RotatableTile(Color.B, Color.B, Color.G, 4);

		assertTrue(board.isValidMove(7, tile1));

		board.setField(13, tile1);

		assertTrue(board.isValidMove(31, tile2));
		// placing outside board index is not allowed
		assertThrows(InvalidIndexException.class, () -> board.isValidMove(-2, tile1));
		assertThrows(InvalidIndexException.class, () -> board.isValidMove(Board.BOARD_SIZE, tile1));

		// placing first move on bonus is invalid
		assertFalse(board.isValidMove(2, tile1));
		assertFalse(board.isValidMove(11, tile1));

		// Valid moves
		assertTrue(board.isValidMove(8, tile1));
		assertTrue(board.isValidMove(15, tile1));
		assertTrue(board.isValidMove(35, tile1));

	}

	@Test
	void testMatchingSides() {
		RotatableTile tile1 = new RotatableTile(Color.B, Color.B, Color.B, 6);
		RotatableTile tile2 = new RotatableTile(Color.B, Color.B, Color.R, 5);
		RotatableTile tile3 = new RotatableTile(Color.G, Color.G, Color.Y, 4);
		board.setField(27, tile1);
		board.setField(28, tile2);
		board.setField(6, tile3);

		//
		assertEquals(-1, board.matchingSides(27, tile1));
		assertEquals(0, board.matchingSides(6, tile3));

	}

	@Test
	void testIndex2Coord() throws InvalidIndexException {
		ArrayList<Integer> list1 = new ArrayList<>();
		list1.add(4);
		list1.add(1);

		ArrayList<Integer> list2 = new ArrayList<>();
		list2.add(4);
		list2.add(-3);

		assertEquals(list1, Board.index2Coord(21));
		assertEquals(list2, Board.index2Coord(17));

	}

	@Test
	void testCoord2Index() {
		int row = 3;
		int column = 1;

		assertEquals(13, Board.coord2Index(row, column));

		int row1 = 5;
		int column1 = 5;

		assertEquals(35, Board.coord2Index(row1, column1));

	}

	@Test
	void testCopy() {
		RotatableTile tile = new RotatableTile(Color.G, Color.G, Color.G, 6);
		board.setField(0, tile);
		Board deepCopy = board.copy();
		deepCopy.setField(0, tile);

		assertEquals(tile, board.getTile(0));
		assertEquals(tile, deepCopy.getTile(0));
	}

	@Test
	void testGetField() {
		assertThrows(IndexOutOfBoundsException.class, () -> board.getField(-2));
		assertThrows(IndexOutOfBoundsException.class, () -> board.getField(Board.BOARD_SIZE));

		assertEquals(0, board.getField(0).getIndex());
		assertEquals(15, board.getField(15).getIndex());
		assertEquals(Board.BOARD_SIZE - 1, board.getField(Board.BOARD_SIZE - 1).getIndex());
	}

	@Test
	void testHasTile() {
		RotatableTile tile1 = new RotatableTile(Color.R, Color.R, Color.R, 6);
		RotatableTile tile2 = new RotatableTile(Color.B, Color.Y, Color.G, 1);
		board.setField(0, tile1);
		board.setField(16, tile2);

		assertTrue(board.hasTile(0), "RRR6");
		assertTrue(board.hasTile(16), "BYG1");
	}

	@Test
	void testGetTileAndSetField() {

		// test for getting tile placed in a field
		RotatableTile tile = new RotatableTile(Color.B, Color.B, Color.B, 6);
		board.setField(0, tile);

		assertEquals(tile, board.getTile(0));

		// testing that empty space on board has no tile
		assertTrue(board.getTile(27) == null);

	}

	@Test
	void testUnEmptyBoard() {
		board.unEmptyBoard();

		assertFalse(board.isEmptyBoard());

	}

}
