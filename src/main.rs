use pleco::{Board, Player, Piece, BitMove, SQ, MoveList};
use std::{io,time::Instant, f32};

const MINIMUM_EVAL: i32 = -2_147_483_647;
const MAXIMUM_EVAL: i32 = 2_147_483_647;
const MAX_EXTENSIONS: u8 = 8;
const TRANSPOSITION_OBJECT_BYTES: usize = 16;
const MB_TO_ITEMS: usize = 1024 * 1024 / TRANSPOSITION_OBJECT_BYTES;



#[derive(Clone, Copy)]
// Each TranspositionObject is 16 bytes
struct TranspositionObject {
    hash: u64,
    score: i32,
    depth: u8,
    best_move: BitMove,
}

impl TranspositionObject {
    fn new() -> TranspositionObject {
        TranspositionObject {
            hash: 0,
            score: 0,
            depth: 0,
            best_move: BitMove::null(),
        }
    }
}

struct Engine {
    board: Board,
    search_stopped: bool,
    active: bool,
    wtime: u32,
    btime: u32,
    movetime: u32,
    depth: u8,
    instant: Instant,
    nodes: u128,
    hash_table_size_mb: usize,
    transposition_table: Vec<TranspositionObject>,
    entries_filled: u32,
}

impl Engine {

    fn new(hash_size_in_mb:usize) -> Engine {
        Engine { 
            board: Board::start_pos(), 
            search_stopped: true, 
            active: true, 
            wtime: 0, 
            btime: 0, 
            movetime: 0, 
            depth: 20,
            instant: Instant::now(),
            nodes: 0,
            hash_table_size_mb: hash_size_in_mb,
            transposition_table: vec![TranspositionObject::new(); hash_size_in_mb * MB_TO_ITEMS],
            entries_filled: 0,
        }
    }

    fn out_of_time(&self) -> bool {
        if &self.instant.elapsed().as_millis() > &self.movetime.into() {
            true
        }
        else {
            false
        }
    }

    fn re_initialize(&mut self) {
        self.wtime = 0;
        self.btime = 0;
        self.movetime = 0;
        self.nodes = 0;
    }

    fn transposition_find(&self, board:&mut Board) -> TranspositionObject {
        let transpos_object = self.transposition_table[board.zobrist() as usize % (self.hash_table_size_mb * MB_TO_ITEMS)];
        if transpos_object.hash != board.zobrist() {
            return TranspositionObject::new();
        }
        else
        {
            return transpos_object;
        }
    }

    fn transposition_store(&mut self, board:&Board, score:i32, best_move:BitMove, depth:u8) {
        let transpos_object = TranspositionObject {
            hash: board.zobrist(),
            score,
            depth,
            best_move,
        };

        let old_obj = self.transposition_table[board.zobrist() as usize % (self.hash_table_size_mb * MB_TO_ITEMS)];

        if old_obj.hash == 0 {
            self.entries_filled += 1
        }

        self.transposition_table[board.zobrist() as usize % (self.hash_table_size_mb * MB_TO_ITEMS)] = transpos_object;
    }

    fn change_hash_size(&mut self, new_size:usize) {
        self.transposition_table.clear();
        self.hash_table_size_mb = new_size;
        self.transposition_table = vec![TranspositionObject::new(); new_size * MB_TO_ITEMS];
        self.entries_filled = 0;
    }

}

fn futile(board:&Board, depth:u8, alpha:i32) -> bool {

    let stand_pat = evaluate(board);

    let futility_margin: u32 = 300 * depth as u32 * depth as u32;

    if futility_margin as i32 + stand_pat < alpha {
        true
    } else { false }

}

fn gen_and_order_moves(board:&mut Board) -> MoveList {
    let moves = board.generate_moves();

    if moves.len() < 2 {
        return moves;
    }

    let mut moves_scores: Vec<(BitMove, u8)> = Vec::default();

    for i in 0..moves.len() {
        if moves[i].is_capture() {
            moves_scores.push((moves[i],6));
            continue;
        }
        if board.gives_check(moves[i]) {
            moves_scores.push((moves[i],5));
            continue;
        }
        moves_scores.push((moves[i],0));
    }

    moves_scores.sort_by_key(|k| k.1);
    moves_scores.reverse();

    let mut new_moves = board.generate_moves();

    for i in 0..moves_scores.len() {
        new_moves[i] = moves_scores[i].0;
    }

    return new_moves;
}

fn evaluate(board:&Board) -> i32 {
    let mut eval:i32 = 0;

    let game_stage: u8 = { if board.count_all_pieces() < 14 { 1 } else { 0 } };

    static NONE_TABLE: [i32; 64] = [
        0,  0,  0,  0,  0,  0,  0,  0,
        0,  0,  0,  0,  0,  0,  0,  0,
        0,  0,  0,  0,  0,  0,  0,  0,
        0,  0,  0,  0,  0,  0,  0,  0,
        0,  0,  0,  0,  0,  0,  0,  0,
        0,  0,  0,  0,  0,  0,  0,  0,
        0,  0,  0,  0,  0,  0,  0,  0,
        0,  0,  0,  0,  0,  0,  0,  0,
    ];

    static MG_PAWN_TABLE: [i32; 64] = [
        0,  0,  0,  0,  0,  0,  0,  0,
        50, 50, 50, 50, 50, 50, 50, 50,
        10, 10, 20, 30, 30, 20, 10, 10,
         5,  5, 10, 25, 25, 10,  5,  5,
         0,  0,  0, 20, 20,  0,  0,  0,
         5, -5,-10,  0,  0,-10, -5,  5,
         5, 10, 10,-20,-20, 10, 10,  5,
         0,  0,  0,  0,  0,  0,  0,  0
    ];

    static EG_PAWN_TABLE: [i32; 64] = [
        0,  0,  0,  0,  0,  0,  0,  0,
        80, 80, 80, 80, 80, 80, 80, 80,
        50, 50, 50, 50, 50, 50, 50, 50,
        30, 30, 30, 30, 30, 30, 30, 30,
        10, 10, 10, 10, 10, 10, 10, 10,
        10, 10, 10, 10, 10, 10, 10, 10,
        -5, -5, -5, -5, -5, -5, -5, -5,
         0,  0,  0,  0,  0,  0,  0,  0
    ];

    static MG_KNIGHT_TABLE: [i32; 64] = [
        -50,-40,-30,-30,-30,-30,-40,-50,
        -40,-20,  0,  0,  0,  0,-20,-40,
        -30,  0, 10, 15, 15, 10,  0,-30,
        -30,  5, 15, 20, 20, 15,  5,-30,
        -30,  0, 15, 20, 20, 15,  0,-30,
        -30,  5, 10, 15, 15, 10,  5,-30,
        -40,-20,  0,  5,  5,  0,-20,-40,
        -50,-40,-30,-30,-30,-30,-40,-50,
    ];

    static MG_BISHOP_TABLE: [i32; 64] = [
        -20,-10,-10,-10,-10,-10,-10,-20,
        -10,  0,  0,  0,  0,  0,  0,-10,
        -10,  0,  5, 10, 10,  5,  0,-10,
        -10,  5,  5, 10, 10,  5,  5,-10,
        -10,  0, 10, 10, 10, 10,  0,-10,
        -10, 10, 10, 10, 10, 10, 10,-10,
        -10,  5,  0,  0,  0,  0,  5,-10,
        -20,-10,-10,-10,-10,-10,-10,-20,
    ];

    static MG_ROOK_TABLE: [i32; 64] = [
        0,  0,  0,  0,  0,  0,  0,  0,
        5, 10, 10, 10, 10, 10, 10,  5,
       -5,  0,  0,  0,  0,  0,  0, -5,
       -5,  0,  0,  0,  0,  0,  0, -5,
       -5,  0,  0,  0,  0,  0,  0, -5,
       -5,  0,  0,  0,  0,  0,  0, -5,
       -5,  0,  0,  0,  0,  0,  0, -5,
        0,  0,  0,  5,  5,  0,  0,  0
    ];

    static MG_QUEEN_TABLE: [i32; 64] = [
        -20,-10,-10, -5, -5,-10,-10,-20,
        -10,  0,  0,  0,  0,  0,  0,-10,
          0,  0,  5, -5, -5,  5,  0,  0,
         -5,  0, -5,  5,  5, -5,  0, -5,
         -5,  0, -5,  5,  5, -5,  0, -5,
        -10,  5,  5, -5, -5,  5,  5,-10,
        -10,  0,  5,  0,  0,  5,  0,-10,
        -20,-10,-10, -5, -5,-10,-10,-20
    ];

    static MG_KING_TABLE: [i32; 64] = [
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -20,-30,-30,-40,-40,-30,-30,-20,
        -10,-20,-20,-20,-20,-20,-20,-10,
         20, 20,  0,  0,  0,  0, 20, 20,
         20, 30, 10,  0,  0, 10, 30, 20
    ];

    static EG_KING_TABLE: [i32; 64] = [
        -50,-40,-30,-20,-20,-30,-40,-50,
        -30,-20,-10,  0,  0,-10,-20,-30,
        -30,-10, 20, 30, 30, 20,-10,-30,
        -30,-10, 30, 40, 40, 30,-10,-30,
        -30,-10, 30, 40, 40, 30,-10,-30,
        -30,-10, 20, 30, 30, 20,-10,-30,
        -30,-30,  0,  0,  0,  0,-30,-30,
        -50,-30,-30,-30,-30,-30,-30,-50
    ];

    static PIECE_TABLES_ALL: [[[i32; 64]; 7]; 2] = [
        [
            NONE_TABLE, MG_PAWN_TABLE, MG_KNIGHT_TABLE, MG_BISHOP_TABLE, MG_ROOK_TABLE, MG_QUEEN_TABLE, MG_KING_TABLE
        ],
        [
            NONE_TABLE, EG_PAWN_TABLE, MG_KNIGHT_TABLE, MG_BISHOP_TABLE, MG_ROOK_TABLE, MG_QUEEN_TABLE, EG_KING_TABLE
        ]
    ];

    static PIECE_VALUES: [i32; 7] = [
        0, 100, 320, 330, 500, 900, 0
    ];

    if board.checkmate() {
        let x:i32 = board.moves_played().into();
        if board.turn() == Player::White {
            return -9999999 + x;
        } else {
            return 9999999 - x;
        }
    }
    if board.stalemate() {
        return 0;
    }
    for location in 0..64 {
        let square = SQ(location);
        let piece: Piece = board.piece_at_sq(square);

        if piece == Piece::None { continue };

        if piece as usize % 8 != piece as usize {
            eval -= PIECE_VALUES[piece as usize % 8];
        } else {
            eval += PIECE_VALUES[piece as usize % 8];
        }

        
        if piece.player().unwrap() == Player::White 
        {
            eval += PIECE_TABLES_ALL[game_stage as usize][piece.type_of() as usize][63-location as usize];
        } 
        else if piece.player().unwrap() == Player::Black 
        {
            eval -= PIECE_TABLES_ALL[game_stage as usize][piece.type_of() as usize][location as usize];
        }
    }
    eval
}

fn minimax(engine:&mut Engine, board:&mut Board, depth:u8, mut alpha:i32, mut beta:i32, search_extensions: u8) -> (BitMove, i32) {
    let moves = gen_and_order_moves(board); // gen moves and order
    if depth == 0 || moves.is_empty() {
        (*engine).nodes += 1;
        return (BitMove::null(), evaluate(board));
    }

    let possible_transposition = (*engine).transposition_find(board);
    if possible_transposition.best_move != BitMove::null() {

        if possible_transposition.depth >= depth {
            return (possible_transposition.best_move, possible_transposition.score);
        }


    }


    if (*engine).out_of_time() {
        return 
            if board.turn() == Player::White 
            {(BitMove::null(),-1)} 
            else 
            {(BitMove::null(),-1)}
    }

    let mut best_move = BitMove::null();

    if board.turn() == Player::White {
        for mv in moves {
            board.apply_move(mv);
            let eval = {
                if (mv.is_capture()||board.in_check()) && search_extensions < MAX_EXTENSIONS {
                    minimax(engine, board, depth, alpha, beta, search_extensions + 1)
                }
                else 
                {
                    if depth > 3 {
                        minimax(engine, board, depth - 1, alpha, beta, search_extensions)
                    }
                    else {
                        if futile(board, depth, alpha) {
                            (mv, alpha - 2)
                        }
                        else {
                            minimax(engine, board, depth - 1, alpha, beta, search_extensions)
                        }
                    }
                    
                }
            };
            board.undo_move();

            if eval.0.is_null() && eval.1 == -1 {
                return (BitMove::null(),-1);
            }

            if alpha < eval.1 {
                alpha = eval.1;
                best_move = mv;
            }
            
            if beta <= alpha {
                break;
            }
        }
        (*engine).transposition_store(board, alpha, best_move, depth);
        return (best_move,alpha)
    }
    else {
        for mv in moves {
            board.apply_move(mv);
            let eval = {
                if (mv.is_capture()||board.in_check()) && search_extensions < MAX_EXTENSIONS {
                    minimax(engine, board, depth, alpha, beta, search_extensions + 1)
                }
                else 
                {

                    if depth > 3 {
                        minimax(engine, board, depth - 1, alpha, beta, search_extensions)
                    }
                    else {
                        if futile(board, depth, -beta) {
                            (mv, beta + 2)
                        }
                        else {
                            minimax(engine, board, depth - 1, alpha, beta, search_extensions)
                        }
                    }
                }
            };
            board.undo_move();

            if eval.0.is_null() && eval.1 == -1 {
                return (BitMove::null(),-1);
            }


            if eval.1 < beta {
                beta = eval.1;
                best_move = mv;
            }
            if beta <= alpha {
                break;
            }
        }
        (*engine).transposition_store(board, beta, best_move, depth);
        return (best_move,beta)
    }
}

fn search(engine:&mut Engine) {

    let mut shallow_board = (*engine).board.shallow_clone();
    
    let mut depth = 0;

    let mut best_move_info: (BitMove, i32) = (BitMove::null(), 0);

    (*engine).instant = Instant::now();

    let perspective = {
        if (*engine).board.turn() == Player::White {1} else {-1}
    };

    while !(*engine).out_of_time() && depth < (*engine).depth {
        let past_best_move_info = best_move_info;

        depth += 1;

        best_move_info = minimax(
            engine,
            &mut shallow_board, 
            depth, 
            MINIMUM_EVAL, 
            MAXIMUM_EVAL,
            MAX_EXTENSIONS,
        );

        if (*engine).out_of_time() {
            /*if past_best_move_info.1 * perspective > best_move_info.1 * perspective {
                best_move_info = past_best_move_info;
            }*/
            best_move_info = past_best_move_info;
        }

        let pv = best_move_info.0;

        println!("info depth {depth} time {} nodes {} score cp {} pv {}",(*engine).instant.elapsed().as_millis(),(*engine).nodes, best_move_info.1 * perspective, pv);
        
        //DEBUG (transposition table)
        //println!("debug-transposition table filled: {} MB/{}.0 MB", (*engine).entries_filled as f64 / MB_TO_ITEMS as f64,((*engine).hash_table_size_mb));

    }

    println!("bestmove {}", best_move_info.0);
}

#[allow(unused)]
fn com(text:&String, engine:&mut Engine) {
    let split_line = text.trim().split(" ");

    let lvec: Vec<&str> = split_line.collect();

    (*engine).re_initialize();

    match lvec[0] {
        "position" => {
            
            match lvec[1] {

                "startpos" => {
                    (*engine).board = Board::start_pos();
                    // to determine whether an input is "position startpos"
                    // or "position startpos moves xxxx xxxx"
                    let mut there_are_moves = false;

                    for word in lvec {

                        if word.trim() == "moves" {
                            there_are_moves = true;
                            continue;
                        }

                        if there_are_moves {
                            let success = (*engine).board.apply_uci_move(word.trim());
                            assert!(success);
                        }

                    }
                }
                    
                "fen" => {

                    let mut there_are_moves = false;

                    let mut fen_constructing = false;

                    let mut fen_string: String = String::new().to_owned();

                    for word in &lvec {

                        match word.trim() {

                            "fen" => {
                                fen_constructing = true;
                                continue;
                            }

                            "moves" => {
                                fen_constructing = false;
                                there_are_moves = true;
                                break;
                            }

                            _ => {
                                if fen_constructing {
                                    fen_string += word;
                                    fen_string += " ";
                                    continue;
                                } else {
                                    continue;
                                }
                            },

                        }
                    }

                    (*engine).board = Board::from_fen(&fen_string).unwrap_or_default();

                    if there_are_moves {
                        
                        let mut flag = false;

                        for word in &lvec {
                            if !flag {
                                match word.trim() {

                                    "moves" => {
                                        flag = true;
                                        continue;
                                    },
    
                                    _ => continue,
    
                                }
                            }
                            
                            let success = (*engine).board.apply_uci_move(word.trim());
                            assert!(success);

                        }
                        
                    }

                }

                _ => {
                    println!("Unknown command: {}", text.trim())
                }
            }
            
            
            
            
        }
        
        "go" => {

            for i in 1..lvec.len() {

                match lvec[i] {

                    "depth" => {
                        (*engine).depth = lvec[i+1].trim().parse::<u8>().unwrap_or_default(); 
                    }

                    "wtime" => {
                        (*engine).wtime = lvec[i+1].trim().parse::<u32>().unwrap_or_default();
                    }

                    "btime" => {
                        (*engine).btime = lvec[i+1].trim().parse::<u32>().unwrap_or_default();
                    }

                    "movetime" => {
                        (*engine).movetime = lvec[i+1].trim().parse::<u32>().unwrap_or_default();
                    }

                    _ => continue,

                }
            }

            (*engine).movetime = {
                if (*engine).movetime != 0 {
                    (*engine).movetime
                }
                else if ((*engine).wtime != 0) || ((*engine).btime != 0) {
                    if (*engine).board.turn() == Player::White {
                        10*f32::sqrt((*engine).wtime as f32) as u32
                    } else {
                        10*f32::sqrt((*engine).btime as f32) as u32
                    }
                }
                else {
                    8000
                }
            };


            (*engine).search_stopped = false;
            search(engine)
        }
        
        "setoption" => {
            match lvec[1] {
                "name" => {
                    match lvec[2] {

                        "Hash" => {
                            match lvec[3] {
                                "value" => {
                                    (*engine).change_hash_size(lvec[4].parse().expect("failed"));
                                }

                                _ => println!("Unknown command: {}\n Try `setoption name Hash value _`", text.trim())
                            }
                        }


                        _ => println!("Unknown command: {}\n Maybe try `uci` and use a valid id from there?", text.trim())
                    }
                }

                _ => println!("Unknown command: {}\n Maybe try setoption `name`?", text.trim())
            }
        }


        "d" => {
            (*engine).board.pretty_print()
        }
        "uci" => {
            println!("id name TissousleBot");
            println!("id author Tissousle");
            println!("");
            println!("option name Hash type spin default 16 min 1 max 4096");
            println!("uciok");
        },
        "isready" => 
            println!("readyok"),
        "ucinewgame" => 
            (),
        "stop" => 
            (*engine).search_stopped = true,
        "quit" =>
            (*engine).active = false,
        _ => 
            println!("Unknown command: {}", text.trim()),
    }
}

fn main() {
    
    

    let mut engine = //std::thread::Builder::new().stack_size(12_000_000).spawn(|| {
        Engine::new(16);
    //}).unwrap().join().unwrap();

    

    while engine.active {

        let mut text = String::new();

        io::stdin()
            .read_line(&mut text)
            .expect("Failed to read line");

        com(&text, &mut engine);

        
    }

}
