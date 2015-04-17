-- 2048.hs: 2048 player

import Data.Array
import Data.List
import Data.Maybe
import System.Random
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Trans.Maybe

--
-- General stuff
--

funcProd :: (a -> b) -> (c -> d) -> ((a,c) -> (b,d))
funcProd f g (a,c) = (f a, g c)

listFuncProd :: ([a] -> [b]) -> ([c] -> [d]) -> ([(a,c)]) -> ([(b,d)])
listFuncProd f g l = zip (f l1) (g l2)
	where (l1,l2) = unzip l

asLongAs :: (a -> Bool) -> a -> Maybe a
asLongAs p x = if p x then Just x else Nothing

-- Takes the mean of a list, returning Nothing if the list is empty
mean :: Fractional a => [a] -> Maybe a
mean [] = Nothing
mean l = Just ((foldr1 (+) l) / (fromIntegral $ length l))

-- Fails with the given value
failWith :: a -> Maybe a -> a
failWith f Nothing = f
failWith f (Just a) = a

-- Finds a maximal element of a list according to the given order, returning Nothing if the list is empty
listMax :: (a -> a -> Ordering) -> [a] -> Maybe a
listMax leq [] = Nothing
listMax cmp (a:as) =
    case listMax cmp as of
	Nothing -> Just a
	Just b -> if a `cmp` b == GT then Just a else Just b

ignoreFailure :: Monad m => MaybeT m a -> m a
ignoreFailure (MaybeT m) = m >>= return . fromJust

--
-- Board basics
--

-- The dimension of the board
dim = 4

-- A tile rank is an integer; a tile of rank 2^n is represented by n
type TileRank = Int

-- The winning tile rank
winningTileRank = 11

data SquareContents = Blank | Tile TileRank
	deriving (Show,Eq)

-- A board location is a pair of integers from 0 to dim-1: it is (x coordinate, y coordinate)
type BoardLoc = (Int,Int)
boardLocs = [(x,y) | x <- [0..dim-1], y <- [0..dim-1]]

type Square = (BoardLoc,SquareContents)

-- A board is a 4x4 array of square contents
type Board = Array BoardLoc SquareContents

-- Makes a board
makeBoard :: [(BoardLoc,SquareContents)] -> Board
makeBoard = array ((0,0),(dim-1,dim-1))

emptyBoard = makeBoard [(i,Blank) | i <- boardLocs]

-- Lists all blank squares in a board
blankSquares :: Board -> [(Int,Int)]
blankSquares board = [i | i <- boardLocs, board!i == Blank]

-- Lists all possible ways of adding a new tile to a board: i.e., moves the computer can make
possibleComputerMoves :: Board -> [Board]
possibleComputerMoves board = [board // [(i,t)] | i <- blankSquares board, t <- [Tile 1, Tile 2]]

-- Lists all possible starting boards, which have two new tiles on them
possibleStartingBoards :: [Board]
possibleStartingBoards = return emptyBoard >>= possibleComputerMoves >>= possibleComputerMoves

-- Says whether a square content is a winning tile
isWinningTile :: SquareContents -> Bool
isWinningTile Blank = False
isWinningTile (Tile n) = n >= winningTileRank

-- Looks for a tile of the winning rank (or greater)
containsWinningTile :: Board -> Bool
containsWinningTile board = foldr (||) False $ map isWinningTile $ elems board

-- Scores the point value of a board
boardScore :: Board -> Int
boardScore board = foldr (+) 0 $ map squareScore $ elems board

-- Scores the point value of a square
squareScore :: SquareContents -> Int
squareScore Blank = 0
squareScore (Tile n) = 2^n

-- Finds the maximum tile score in a board
maxTileScore :: Board -> Int
maxTileScore board = 2^(maxTileRank board)

maxTileRank board = fromJust $ listMax compare (elems board >>= extractRanks)

extractRanks Blank = []
extractRanks (Tile n) = [n]

--
-- Executing player moves
--

-- Merges the matching pairs in a list of squares, without padding with blanks
mergeMatchingPairs :: [SquareContents] -> [SquareContents]
mergeMatchingPairs (Tile n : Tile m : l) =
	if n == m then Tile (n+1) : mergeMatchingPairs l
	else Tile n : mergeMatchingPairs (Tile m: l)
mergeMatchingPairs l = l

-- Pads a list of squares with blanks at the right
padWithBlanks l = l ++ replicate (dim - (length l)) Blank

-- Carries out the result of a move to the left on a list of squares
moveToLeft :: [SquareContents] -> [SquareContents]
moveToLeft l = padWithBlanks $ mergeMatchingPairs $ filter (/= Blank) l

-- A movement direction is a pair of integers: (0,1) bottom-to-top, (0,-1) top-to-bottom, (1,0) LTR, (-1,0) RTL
type MovementDir = (Int,Int)
movementDirs = [(0,1),(0,-1),(1,0),(-1,0)]

data RowOrCol = Row | Col
	deriving Eq

-- Gives row or column i of the board, LTR/top-to-bottom if direction is 1 or RTL/bottom-to-top if direction is -1
boardRowOrCol :: Board -> Int -> Int -> RowOrCol -> [(BoardLoc,SquareContents)]
boardRowOrCol board i direction rowOrCol = f [(g (i,j), board!(g (i,j))) | j <- [0..dim-1]]
	where f = case (direction,rowOrCol) of
			(1,Row) -> reverse
			(-1,Row) -> id
			(1,Col) -> id
			(-1,Col) -> reverse
	      g = if rowOrCol == Row then (\(a,b) -> (b,a)) else id

-- Gives all {rows,columns} in a board LTR/top-to-bottom or RTL/bottom-to-top
boardRowsOrCols :: Board -> Int -> RowOrCol -> [[(BoardLoc,SquareContents)]]
boardRowsOrCols board direction rowOrCol = [boardRowOrCol board i direction rowOrCol | i <- [0..dim-1]]

-- Executes a player move, without regard to whether that move changes the board
executePlayerMoveUnconditionally :: Board -> MovementDir -> Board
executePlayerMoveUnconditionally board (xdir,ydir) = makeBoard $ concatMap (id `listFuncProd` moveToLeft) $ boardRowsOrCols board dir rowOrCol
	where dir = xdir + ydir
	      rowOrCol = if xdir /= 0 then Row else Col

-- Executes a player move, as long as that move changes the board
executePlayerMove :: Board -> MovementDir -> Maybe Board
executePlayerMove board dir = asLongAs (/= board) $ executePlayerMoveUnconditionally board dir

--
-- Evaluating terminal positions
--

-- The terminal position evaluation judges the value of a position
-- one square at a time. It judges the top half of the board by regarding
-- high ranked tiles early in the order of squares proceeding from 
-- left to right in the first row then right to left in the second row
-- as valuable. It judges the bottom half of the board by regarding all tiles
-- as a liability, with higher value tiles being a greater liability.
--
-- XXX: Constants hard coded for now; should become part of the control

evalSquares :: GameControl -> Board -> Float
evalSquares ctrl board = foldr (+) 0 $ map (evalSquare ctrl board) boardLocs

evalSquare :: GameControl -> Board -> BoardLoc -> Float
evalSquare ctrl board loc =
  squarePositionalValue ctrl (loc, board!loc)

squarePositionalValue :: GameControl -> Square -> Float
squarePositionalValue ctrl square@((x,y),c) =
  if y <= 1 then highSquarePositionalValue ctrl square else lowSquarePositionalValue ctrl square

-- Gives the ordinal position in the canonical order of high squares, counting from 1
highSquareOrdinalPos :: BoardLoc -> Int
highSquareOrdinalPos (x,y) = case y of
  0 -> 1+x
  1 -> 4 + (4 - x)
  _ -> error "Fed a bad location to highSquareOrdinalPos"

highSquarePositionalValue ctrl (loc, Blank) = 0
highSquarePositionalValue ctrl (loc, Tile rank) =
  2^(2*rank) * (highTileLocCoef ctrl (highSquareOrdinalPos loc) rank)

highTileLocCoef ctrl pos rank = 2^(8-pos)

lowSquarePositionalValue ctrl ((x,y),Blank) =
  case y of {
    2 -> 32;
	3 -> 128;
	_ -> error "Bad y value to lowSquarePositionalValue"
  }

lowSquarePositionalValue ctrl ((x,y),Tile rank) = -2^rank * ycoef
  where ycoef = case y of {
	  2 -> 1;
	  3 -> 2^rank;
	  _ -> error "Bad y value to lowSquarePositionalValue"
	}

evaluateTerminalPosition :: GameControl -> Board -> Float
evaluateTerminalPosition = evalSquares

--
-- Evaluating positions
--

-- Takes a position, looks at all possible computer moves from that position, and determines
-- their average value according to the given utility function, returning valueOfLoss if the
-- computer has no moves because the board is full.
evaluateByOnComputersTurn :: GameControl -> (Board -> Float) -> Board -> Float
evaluateByOnComputersTurn ctrl utility board = failWith (valueOfLoss ctrl) $
  mean (map utility $ possibleComputerMoves board)

-- Takes a position, looks at all possible player moves from that position, and returns
-- a list of their values according to the given utility function.
evaluatePlayerMovesBy :: (Board -> Float) -> Board -> [(MovementDir,Float)]
evaluatePlayerMovesBy utility board =
	movementDirs >>=
	(\dir -> [dir] `zip` maybeToList (executePlayerMove board dir)) >>=
	return . (id `funcProd` utility)

-- Takes a position, looks at all possible player moves from that position, and returns
-- a maximally good move and its utility according to the given function, if a move is available.
bestPlayerMoveBy :: (Board -> Float) -> Board -> Maybe (MovementDir,Float)
bestPlayerMoveBy utility board = listMax cmp (evaluatePlayerMovesBy utility board)
	where (d1,a) `cmp` (d2,b) = a `compare` b

-- Evaluates a position to a given search depth on the computer's turn.
evaluateOnComputersTurn :: GameControl -> Int -> Board -> Float
evaluateOnComputersTurn ctrl 0 board = evaluateTerminalPosition ctrl board
evaluateOnComputersTurn ctrl depth board =
  evaluateByOnComputersTurn ctrl (evaluateOnPlayersTurn ctrl depth) board

-- Evaluates a position to a given search depth on the player's turn.
evaluateOnPlayersTurn :: GameControl -> Int -> Board -> Float
evaluateOnPlayersTurn ctrl depth board = failWith (valueOfLoss ctrl) $
    bestPlayerMoveBy (evaluateOnComputersTurn ctrl (depth-1)) board >>= return . snd

-- Returns a maximally good move for a player, if there is a move available.
bestPlayerMove :: GameControl -> Board -> Maybe MovementDir
bestPlayerMove ctrl board =
  bestPlayerMoveBy (evaluateOnComputersTurn ctrl (searchDepth ctrl)) board
    >>= return . fst

--
-- Playing a game
--

-- The parameters controlling the game AI
data GameControl = GameControl {
	searchDepth :: Int,
	valueOfLoss :: Float
}

defaultControls = GameControl {
	searchDepth = 2,
	valueOfLoss = -2^24
}

-- The mutable state of a game: an infinite list of random numbers, and the board
data Game = Game {
	control :: GameControl,
	rands :: [Int],
	board :: Board
}

type GameState = State Game

-- Makes a new game with an empty board given a random number generator and a control
newEmptyGame :: StdGen -> GameControl -> Game
newEmptyGame gen ctrl = Game { rands = randoms gen, board = emptyBoard, control = ctrl }

-- Initializes a game: sets the board to empty and then makes two computer moves.
initGame :: GameState ()
initGame =
 do st <- get
    put st { board = emptyBoard }
    ignoreFailure doComputerMove
    ignoreFailure doComputerMove

-- Gets a random number from the game's random number generator
getGameRandom :: GameState Int
getGameRandom =
  do st <- get
     put st { rands = tail (rands st)}
     return $ head $ rands st

-- Makes the computer move in a game, failing if no move was possible.
doComputerMove :: MaybeT GameState ()
doComputerMove =
  do r <- lift getGameRandom
     st <- lift get
     let boards = possibleComputerMoves (board st)
     guard (boards /= [])
     let newBoard = boards !! (r `mod` (length boards))
     lift $ put st {board = newBoard}

-- Makes the player move in a game, failing if no move was possible
doPlayerMove :: MaybeT GameState ()
doPlayerMove =
  do st <- lift get
     move <- MaybeT $ return $ bestPlayerMove (control st) (board st)
     lift $ put st { board = executePlayerMoveUnconditionally (board st) move }

-- Runs a turn in the game (player then computer)
doTurn :: MaybeT GameState ()
doTurn = doPlayerMove >> doComputerMove

-- The outcome of a game: either win, or loss with score and maximum tile achieved
data GameOutcome = Win | Loss Int Int
  deriving Show

-- Runs a game, returning True if the player won
runGame :: GameState GameOutcome
runGame =
  do initGame
     playGame

playGame :: GameState GameOutcome
playGame =
  do st <- get
     let play = (lift $ put st) >> doTurn
     case runState (runMaybeT play) st of
       (Just (), st') ->
         do put st'
            if containsWinningTile (board st') then return Win
              else playGame
       (Nothing, st') -> return (Loss (boardScore $ board st') (maxTileScore $ board st'))

--
-- Main
--

main :: IO ()
main = do
  gen <- getStdGen
  let game = newEmptyGame gen defaultControls
  let out = fst $ runState runGame game
  print out
