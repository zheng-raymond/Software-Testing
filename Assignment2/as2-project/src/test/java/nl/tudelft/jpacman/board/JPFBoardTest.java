package nl.tudelft.jpacman.board;

import static org.junit.Assert.*;
import static org.mockito.Mockito.mock;

import org.junit.Before;
import org.junit.Test;

public class JPFBoardTest {
	private Board board;
	
	private final Square x0y0 = mock(Square.class);
	private final Square x0y1 = mock(Square.class);
	private final Square x0y2 = mock(Square.class);
	private final Square x1y0 = mock(Square.class);
	private final Square x1y1 = mock(Square.class);
	private final Square x1y2 = mock(Square.class);
	
	private static final int MAX_WIDTH = 2;
	private static final int MAX_HEIGHT = 3;
	
	/**
	 * Setup a board that can be used for testing.
	 */
	@Before
	public void setUp() {
		Square[][] grid = new Square[MAX_WIDTH][MAX_HEIGHT];
		grid[0][0] = x0y0;
		grid[0][1] = x0y1;
		grid[0][2] = x0y2;
		grid[1][0] = x1y0;
		grid[1][1] = x1y1;
		grid[1][2] = x1y2;
		board = new Board(grid);
	}
	

 //test withinBorders() with return value of true , on board
	@Test
	public void testWithinBorders1(){
		assertEquals(true, board.withinBorders(0, 0));
	}
	
	
	 //test withinBorders() with return value of false, off board
	 
	@Test
	public void testWithinBorders2(){
		assertEquals(false, board.withinBorders(0, 3));
	}
	

	 //test withinBorders() with return value of false, off board
	@Test
	public void testWithinBorders3(){
		assertEquals(false, board.withinBorders(0, -1000000));
	}

	 //test withinBorders() with return value of false , off board
	@Test
	public void testWithinBorders4(){
		assertEquals(false, board.withinBorders(2,-2147483648));
	}
	
	//test withinBorders() with return value of false, off board
	@Test
	public void testWithinBorders5(){
		assertEquals(false, board.withinBorders(-1000000,-2147483648));
	}
	
    //the test only contains off board and on board but no in board
    //test withinBorders() with return value of true , in board
	@Test
	public void testWithinBorders6(){
		assertEquals(true, board.withinBorders(1,1));
	}
}
