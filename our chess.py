import io
import random

import PySimpleGUI as sg
from stockfish import Stockfish
import os
import sys
import subprocess
import threading
from pathlib import Path, PurePath
import queue
import copy
import time
from datetime import datetime
import json
import chess
import chess.pgn
import chess.engine
import chess.polyglot
import logging
import re

moves = []
kkk = 0
game = 1
move_list = None
active = False
index = 0

APP_NAME = 'Best Chess Game'
BOX_TITLE = f'{APP_NAME}'

lista = ["1.Kasparov vs the world", "2.Random game generated", "3.Random game generated", "4.Random game generated",
         "5.Caruana Fabiano vs Carlen Magnus WCh 2018",
         "6.Carlen Magnus vs Caruana Fabiano WCh 2018", "7.Carlsen Magnus vs Karjakin Sergey WCh 2016",
         "8.Karjakin Sergey vs Carlsen Magnus WCh 2016", "9.Kramnik V vs Svidler P WCh 2007"]

MIN_DEPTH = 1
MAX_DEPTH = 1000
GUI_THEME = ['Green', 'GreenTan', 'LightGreen', 'BluePurple', 'Purple',
             'BlueMono', 'GreenMono', 'BrownBlue', 'BrightColors',
             'NeutralBlue', 'Kayak', 'SandyBeach', 'TealMono', 'Topanga',
             'Dark', 'Black', 'DarkAmber']

BLANK = 0
PAWNB = 1
KNIGHTB = 2
BISHOPB = 3
ROOKB = 4
KINGB = 5
QUEENB = 6
PAWNW = 7
KNIGHTW = 8
BISHOPW = 9
ROOKW = 10
KINGW = 11
QUEENW = 12

RANK_8 = 7
RANK_7 = 6
RANK_6 = 5
RANK_5 = 4
RANK_4 = 3
RANK_3 = 2
RANK_2 = 1
RANK_1 = 0

initial_board = [[ROOKB, KNIGHTB, BISHOPB, QUEENB, KINGB, BISHOPB, KNIGHTB, ROOKB],
                 [PAWNB, ] * 8,
                 [BLANK, ] * 8,
                 [BLANK, ] * 8,
                 [BLANK, ] * 8,
                 [BLANK, ] * 8,
                 [PAWNW, ] * 8,
                 [ROOKW, KNIGHTW, BISHOPW, QUEENW, KINGW, BISHOPW, KNIGHTW, ROOKW]]

white_init_promote_board = [[QUEENW, ROOKW, BISHOPW, KNIGHTW]]

black_init_promote_board = [[QUEENB, ROOKB, BISHOPB, KNIGHTB]]

IMAGE_PATH = 'Images/80'
blank = os.path.join(IMAGE_PATH, 'blank.png')
bishopB = os.path.join(IMAGE_PATH, 'bB.png')
bishopW = os.path.join(IMAGE_PATH, 'wB.png')
pawnB = os.path.join(IMAGE_PATH, 'bP.png')
pawnW = os.path.join(IMAGE_PATH, 'wP.png')
knightB = os.path.join(IMAGE_PATH, 'bN.png')
knightW = os.path.join(IMAGE_PATH, 'wN.png')
rookB = os.path.join(IMAGE_PATH, 'bR.png')
rookW = os.path.join(IMAGE_PATH, 'wR.png')
queenB = os.path.join(IMAGE_PATH, 'bQ.png')
queenW = os.path.join(IMAGE_PATH, 'wQ.png')
kingB = os.path.join(IMAGE_PATH, 'bK.png')
kingW = os.path.join(IMAGE_PATH, 'wK.png')

images = {BISHOPB: bishopB, BISHOPW: bishopW, PAWNB: pawnB, PAWNW: pawnW,
          KNIGHTB: knightB, KNIGHTW: knightW,
          ROOKB: rookB, ROOKW: rookW, KINGB: kingB, KINGW: kingW,
          QUEENB: queenB, QUEENW: queenW, BLANK: blank}

# # Promote piece from psg (pysimplegui) to pyc (python-chess)
promote_psg_to_pyc = {KNIGHTB: chess.KNIGHT, BISHOPB: chess.BISHOP,
                      ROOKB: chess.ROOK, QUEENB: chess.QUEEN,
                      KNIGHTW: chess.KNIGHT, BISHOPW: chess.BISHOP,
                      ROOKW: chess.ROOK, QUEENW: chess.QUEEN, }

INIT_PGN_TAG = {
    'Event': 'Human vs AI',
    'White': 'Human',
    'Black': 'AI',
}

menu_def_neutral = [
    ['&Mode', ['Play', 'Exit']],
    ['Boar&d', ['Color', ['Brown::board_color_k',
                          'Blue::board_color_k',
                          'Green::board_color_k',
                          'Gray::board_color_k'],
                'Theme', GUI_THEME]],
    ['&Engine', ['Set Depth']],
    ['Select Match', ['Choose', lista]]]

menu_def_play = [
    ['&Mode', ['Reset', 'Exit']],
    ['Insert game', ['Auto']],
    ['&AI', ['Make move']], ]


class Timer:
    def __init__(self, tc_type='fischer', base=300000, inc=10000,
                 period_moves=40):
        self.tc_type = tc_type
        self.base = base
        self.inc = inc
        self.period_moves = period_moves
        self.elapse = 0
        self.init_base_time = self.base

    def update_base(self):

        if self.tc_type == 'delay':
            self.base += min(0, self.inc - self.elapse)
        elif self.tc_type == 'fischer':
            self.base += self.inc - self.elapse
        elif self.tc_type == 'timepermove':
            self.base = self.init_base_time
        else:
            self.base -= self.elapse

        self.base = max(0, self.base)
        self.elapse = 0


class RunEngine(threading.Thread):
    pv_length = 9
    move_delay_sec = 3.0

    def __init__(self, eng_queue, engine_config_file, engine_path_and_file,
                 engine_id_name, max_depth=MAX_DEPTH,
                 base_ms=300000, inc_ms=1000, tc_type='fischer',
                 period_moves=0, is_stream_search_info=True):
        threading.Thread.__init__(self)
        self._kill = threading.Event()
        self.engine_config_file = engine_config_file
        self.engine_path_and_file = engine_path_and_file
        self.engine_id_name = engine_id_name
        self.own_book = False
        self.bm = None
        self.pv = None
        self.score = None
        self.depth = None
        self.time = None
        self.nps = 0
        self.max_depth = 2
        self.eng_queue = eng_queue
        self.engine = None
        self.board = None
        self.analysis = is_stream_search_info
        self.is_nomove_number_in_variation = True
        self.base_ms = base_ms
        self.inc_ms = inc_ms
        self.tc_type = tc_type
        self.period_moves = period_moves
        self.is_ownbook = False
        self.is_move_delay = False

    def stop(self):
        self._kill.set()

    def get_board(self, board):
        self.board = board

    def configure_engine(self):

        with open(self.engine_config_file, 'r') as json_file:
            data = json.load(json_file)
            for p in data:
                if p['name'] == self.engine_id_name:
                    for n in p['options']:

                        if n['name'].lower() == 'ownbook':
                            self.is_ownbook = True

                        # Ignore button type for a moment.
                        if n['type'] == 'button':
                            continue

                        if n['type'] == 'spin':
                            user_value = int(n['value'])
                            default_value = int(n['default'])
                        else:
                            user_value = n['value']
                            default_value = n['default']

                        if user_value != default_value:
                            try:
                                self.engine.configure({n['name']: user_value})
                            except Exception:
                                pass

    def run(self):

        folder = Path(self.engine_path_and_file)
        folder = folder.parents[0]

        try:
            self.engine = chess.engine.SimpleEngine.popen_uci(
                self.engine_path_and_file, cwd=folder,
                creationflags=subprocess.CREATE_NO_WINDOW)
        except chess.engine.EngineTerminatedError:
            self.eng_queue.put('bestmove {}'.format(self.bm))
            return
        except Exception:
            self.eng_queue.put('bestmove {}'.format(self.bm))
            return

        # Set engine option values
        try:
            self.configure_engine()
        except Exception:
            pass

        # Set search limits
        if self.tc_type == 'delay':
            limit = chess.engine.Limit(
                depth=self.max_depth if self.max_depth != MAX_DEPTH else None,
                white_clock=self.base_ms / 1000,
                black_clock=self.base_ms / 1000,
                white_inc=self.inc_ms / 1000,
                black_inc=self.inc_ms / 1000)
        elif self.tc_type == 'timepermove':
            limit = chess.engine.Limit(time=self.base_ms / 1000,
                                       depth=self.max_depth if
                                       self.max_depth != MAX_DEPTH else None)
        else:
            limit = chess.engine.Limit(
                depth=self.max_depth if self.max_depth != MAX_DEPTH else None,
                white_clock=self.base_ms / 1000,
                black_clock=self.base_ms / 1000,
                white_inc=self.inc_ms / 1000,
                black_inc=self.inc_ms / 1000)
        start_time = time.perf_counter()
        if self.analysis:
            is_time_check = False

            with self.engine.analysis(self.board, limit) as analysis:
                for info in analysis:

                    if self._kill.wait(0.1):
                        break

                    try:
                        if 'depth' in info:
                            self.depth = int(info['depth'])

                        if 'score' in info:
                            self.score = int(info['score'].relative.score(
                                mate_score=32000)) / 100

                        self.time = info['time'] if 'time' in info \
                            else time.perf_counter() - start_time

                        if 'pv' in info and not ('upperbound' in info or
                                                 'lowerbound' in info):
                            self.pv = info['pv'][0:self.pv_length]

                            if self.is_nomove_number_in_variation:
                                spv = self.short_variation_san()
                                self.pv = spv
                            else:
                                self.pv = self.board.variation_san(self.pv)

                            self.eng_queue.put('{} pv'.format(self.pv))
                            self.bm = info['pv'][0]

                        # score, depth, time, pv
                        if self.score is not None and \
                                self.pv is not None and self.depth is not None:
                            info_to_send = '{:+5.2f} | {} | {:0.1f}s | {} info_all'.format(
                                self.score, self.depth, self.time, self.pv)
                            self.eng_queue.put('{}'.format(info_to_send))

                        # Send stop if movetime is exceeded
                        if not is_time_check and self.tc_type != 'fischer' \
                                and self.tc_type != 'delay' and \
                                time.perf_counter() - start_time >= \
                                self.base_ms / 1000:
                            is_time_check = True
                            break

                        # Send stop if max depth is exceeded
                        if 'depth' in info:
                            if int(info['depth']) >= self.max_depth != MAX_DEPTH:
                                break
                    except Exception:
                        pass
        else:
            result = self.engine.play(self.board, limit, info=chess.engine.INFO_ALL)
            try:
                self.depth = result.info['depth']
            except KeyError:
                self.depth = 1
            try:
                self.score = int(result.info['score'].relative.score(
                    mate_score=32000)) / 100
            except KeyError:
                self.score = 0
            try:
                self.time = result.info['time'] if 'time' in result.info \
                    else time.perf_counter() - start_time
            except KeyError:
                self.time = 0
            try:
                if 'pv' in result.info:
                    self.pv = result.info['pv'][0:self.pv_length]

                if self.is_nomove_number_in_variation:
                    spv = self.short_variation_san()
                    self.pv = spv
                else:
                    self.pv = self.board.variation_san(self.pv)
            except Exception:
                self.pv = None

            if self.pv is not None:
                info_to_send = '{:+5.2f} | {} | {:0.1f}s | {} info_all'.format(
                    self.score, self.depth, self.time, self.pv)
                self.eng_queue.put('{}'.format(info_to_send))
            self.bm = result.move

        if self.is_move_delay:
            while True:
                if time.perf_counter() - start_time >= self.move_delay_sec:
                    break
                time.sleep(1.0)

        if self.bm is None:
            try:
                result = self.engine.play(self.board, limit)
                self.bm = result.move
            except Exception:
                pass
        self.eng_queue.put('bestmove {}'.format(self.bm))

    def quit_engine(self):

        try:
            self.engine.quit()
        except:
            pass

    def short_variation_san(self):

        if self.pv is None:
            return None

        short_san_pv = []
        tmp_board = self.board.copy()
        for pc_move in self.pv:
            san_move = tmp_board.san(pc_move)
            short_san_pv.append(san_move)
            tmp_board.push(pc_move)

        return ' '.join(short_san_pv)


class EasyChessGui:
    queue = queue.Queue()
    is_user_white = True

    def __init__(self, theme, engine_config_file, user_config_file,
                 gui_book_file, computer_book_file, human_book_file,
                 is_use_gui_book, is_random_book, max_book_ply,
                 max_depth=MAX_DEPTH):
        self.theme = theme
        self.user_config_file = user_config_file
        self.engine_config_file = engine_config_file
        self.gui_book_file = gui_book_file
        self.computer_book_file = computer_book_file
        self.human_book_file = human_book_file
        self.max_depth = 2
        self.is_use_gui_book = is_use_gui_book
        self.is_random_book = is_random_book
        self.max_book_ply = max_book_ply
        self.opp_path_and_file = None
        self.opp_file = None
        self.opp_id_name = None
        self.adviser_file = None
        self.adviser_path_and_file = None
        self.adviser_id_name = None
        self.adviser_hash = 128
        self.adviser_threads = 1
        self.adviser_movetime_sec = 10
        self.pecg_auto_save_game = 'pecg_auto_save_games.pgn'
        self.my_games = 'pecg_my_games.pgn'
        self.repertoire_file = {'white': 'pecg_white_repertoire.pgn', 'black': 'pecg_black_repertoire.pgn'}
        self.init_game()
        self.fen = None
        self.psg_board = None
        self.menu_elem = None
        self.engine_id_name_list = []
        self.engine_file_list = []
        self.username = 'Human'

        self.human_base_time_ms = 5 * 60 * 1000  # 5 minutes
        self.human_inc_time_ms = 10 * 1000  # 10 seconds
        self.human_period_moves = 0
        self.human_tc_type = 'fischer'

        self.engine_base_time_ms = 3 * 60 * 1000  # 5 minutes
        self.engine_inc_time_ms = 2 * 1000  # 10 seconds
        self.engine_period_moves = 0
        self.engine_tc_type = 'fischer'

        # Default board color is brown
        self.sq_light_color = '#daf1e3'
        self.sq_dark_color = '#3a7859'
        self.move_sq_light_color = '#bae58f'
        self.move_sq_dark_color = '#6fbc55'
        self.gui_theme = 'Topanga'

        self.is_save_time_left = False
        self.is_save_user_comment = True

    def update_game(self, mc, user_move, time_left, user_comment):

        # Save user comment
        if self.is_save_user_comment:
            # If comment is empty
            if not (user_comment and user_comment.strip()):
                if mc == 1:
                    self.node = self.game.add_variation(user_move)
                else:
                    self.node = self.node.add_variation(user_move)

                # Save clock (time left after a move) as move comment
                if self.is_save_time_left:
                    rem_time = self.get_time_h_mm_ss(time_left, False)
                    self.node.comment = '[%clk {}]'.format(rem_time)
            else:
                if mc == 1:
                    self.node = self.game.add_variation(user_move)
                else:
                    self.node = self.node.add_variation(user_move)

                # Save clock, add clock as comment after a move
                if self.is_save_time_left:
                    rem_time = self.get_time_h_mm_ss(time_left, False)
                    self.node.comment = '[%clk {}] {}'.format(rem_time,
                                                              user_comment)
                else:
                    self.node.comment = user_comment
        # Do not save user comment
        else:
            if mc == 1:
                self.node = self.game.add_variation(user_move)
            else:
                self.node = self.node.add_variation(user_move)

            # Save clock, add clock as comment after a move
            if self.is_save_time_left:
                rem_time = self.get_time_h_mm_ss(time_left, False)
                self.node.comment = '[%clk {}]'.format(rem_time)

    def create_new_window(self, window, flip=False):

        loc = window.CurrentLocation()
        window.Disable()
        if flip:
            self.is_user_white = not self.is_user_white

        layout = self.build_main_layout(self.is_user_white)

        w = sg.Window('{}'.format(APP_NAME),
                      layout,
                      default_button_element_size=(12, 1),
                      auto_size_buttons=False,
                      location=(loc[0], loc[1]), icon='Icon/pecg.png')

        # Initialize White and black boxes
        while True:
            button, value = w.Read(timeout=50)
            self.update_labels_and_game_tags(w, human=self.username)
            break

        window.Close()
        return w

    def get_players(self, pgn, q):
        players = []
        games = 0
        with open(pgn) as h:
            while True:
                headers = chess.pgn.read_headers(h)
                if headers is None:
                    break

                wp = headers['White']
                bp = headers['Black']

                players.append(wp)
                players.append(bp)
                games += 1

        p = list(set(players))
        ret = [p, games]

        q.put(ret)

    def get_engine_id_name(self, path_and_file, q):

        id_name = None
        folder = Path(path_and_file)
        folder = folder.parents[0]

        try:
            engine = chess.engine.SimpleEngine.popen_uci(
                path_and_file, cwd=folder,
                creationflags=subprocess.CREATE_NO_WINDOW)
            id_name = engine.id['name']
            engine.quit()
        except Exception:
            pass

        q.put(['Done', id_name])

    def get_engine_hash(self, eng_id_name):

        eng_hash = None
        with open(self.engine_config_file, 'r') as json_file:
            data = json.load(json_file)
            for p in data:
                if p['name'] == eng_id_name:
                    # There engines without options
                    try:
                        for n in p['options']:
                            if n['name'].lower() == 'hash':
                                return n['value']
                    except KeyError:
                        break
                    except Exception:
                        pass

        return eng_hash

    def get_engine_threads(self, eng_id_name):

        eng_threads = None
        with open(self.engine_config_file, 'r') as json_file:
            data = json.load(json_file)
            for p in data:
                if p['name'] == eng_id_name:
                    try:
                        for n in p['options']:
                            if n['name'].lower() == 'threads':
                                return n['value']
                    except KeyError:
                        break
                    except Exception:
                        pass

        return eng_threads

    def get_engine_file(self, eng_id_name):

        eng_file, eng_path_and_file = None, None
        with open(self.engine_config_file, 'r') as json_file:
            data = json.load(json_file)
            for p in data:
                if p['name'] == eng_id_name:
                    eng_file = p['command']
                    eng_path_and_file = Path(p['workingDirectory'],
                                             eng_file).as_posix()
                    break

        return eng_file, eng_path_and_file

    def get_engine_id_name_list(self):

        eng_id_name_list = []
        with open(self.engine_config_file, 'r') as json_file:
            data = json.load(json_file)
            for p in data:
                if p['protocol'] == 'uci':
                    eng_id_name_list.append(p['name'])

        eng_id_name_list = sorted(eng_id_name_list)

        return eng_id_name_list

    def is_name_exists(self, name):

        with open(self.engine_config_file, 'r') as json_file:
            data = json.load(json_file)

        for p in data:
            jname = p['name']
            if jname == name:
                return True

        return False

    def add_engine_to_config_file(self, engine_path_and_file, pname, que):

        folder = Path(engine_path_and_file).parents[0]
        file = PurePath(engine_path_and_file)
        file = file.name

        option = []

        with open(self.engine_config_file, 'r') as json_file:
            data = json.load(json_file)

        try:
            engine = chess.engine.SimpleEngine.popen_uci(
                engine_path_and_file, cwd=folder,
                creationflags=subprocess.CREATE_NO_WINDOW)
        except Exception:
            que.put('Failure')
            return

        try:
            opt_dict = engine.options.items()
        except Exception:
            que.put('Failure')
            return

        engine.quit()

        for opt in opt_dict:
            o = opt[1]

            if o.type == 'spin':
                # Adjust hash and threads values
                if o.name.lower() == 'threads':
                    value = 1
                elif o.name.lower() == 'hash':
                    value = 32
                else:
                    value = o.default

                option.append({'name': o.name,
                               'default': o.default,
                               'value': value,
                               'type': o.type,
                               'min': o.min,
                               'max': o.max})
            elif o.type == 'combo':
                option.append({'name': o.name,
                               'default': o.default,
                               'value': o.default,
                               'type': o.type,
                               'choices': o.var})
            else:
                option.append({'name': o.name,
                               'default': o.default,
                               'value': o.default,
                               'type': o.type})

        # Save engine filename, working dir, name and options
        wdir = Path(folder).as_posix()
        protocol = 'uci'  # Only uci engine is supported so far
        self.engine_id_name_list.append(pname)
        data.append({'command': file, 'workingDirectory': wdir,
                     'name': pname, 'protocol': protocol,
                     'options': option})

        # Save data to pecg_engines.json
        with open(self.engine_config_file, 'w') as h:
            json.dump(data, h, indent=4)

        que.put('Success')

    def check_engine_config_file(self):

        ec = Path(self.engine_config_file)
        if ec.exists():
            return

        data = []
        cwd = Path.cwd()

        self.engine_file_list = self.get_engines()

        for fn in self.engine_file_list:
            # Run engine and get id name and options
            option = []

            # cwd=current working dir, engines=folder, fn=exe file
            epath = Path(cwd, 'engines', fn)
            engine_path_and_file = str(epath)
            folder = epath.parents[0]

            try:
                engine = chess.engine.SimpleEngine.popen_uci(
                    engine_path_and_file, cwd=folder,
                    creationflags=subprocess.CREATE_NO_WINDOW)
            except Exception:
                continue

            engine_id_name = engine.id['name']
            opt_dict = engine.options.items()
            engine.quit()

            for opt in opt_dict:
                o = opt[1]

                if o.type == 'spin':
                    # Adjust hash and threads values
                    if o.name.lower() == 'threads':
                        value = 1
                    elif o.name.lower() == 'hash':
                        value = 32
                    else:
                        value = o.default

                    option.append({'name': o.name,
                                   'default': o.default,
                                   'value': value,
                                   'type': o.type,
                                   'min': o.min,
                                   'max': o.max})
                elif o.type == 'combo':
                    option.append({'name': o.name,
                                   'default': o.default,
                                   'value': o.default,
                                   'type': o.type,
                                   'choices': o.var})
                else:
                    option.append({'name': o.name,
                                   'default': o.default,
                                   'value': o.default,
                                   'type': o.type})

            # Save engine filename, working dir, name and options
            wdir = Path(cwd, 'Engines').as_posix()
            name = engine_id_name
            protocol = 'uci'
            self.engine_id_name_list.append(name)
            data.append({'command': fn, 'workingDirectory': wdir,
                         'name': name, 'protocol': protocol,
                         'options': option})
        # Save data to pecg_engines.json
        with open(self.engine_config_file, 'w') as h:
            json.dump(data, h, indent=4)

    @staticmethod
    def get_time_mm_ss_ms(time_ms):

        s, ms = divmod(int(time_ms), 1000)
        m, s = divmod(s, 60)

        # return '{:02d}m:{:02d}s:{:03d}ms'.format(m, s, ms)
        return '{:02d}m:{:02d}s'.format(m, s)

    @staticmethod
    def get_time_h_mm_ss(time_ms, symbol=True):

        s, ms = divmod(int(time_ms), 1000)
        m, s = divmod(s, 60)
        h, m = divmod(m, 60)

        if not symbol:
            return '{:01d}:{:02d}:{:02d}'.format(h, m, s)
        return '{:01d}h:{:02d}m:{:02d}s'.format(h, m, s)

    def update_text_box(self, window, msg, is_hide):

        best_move = None
        msg_str = str(msg)
        if 'bestmove ' not in msg_str:
            if 'info_all' in msg_str:
                info_all = ' '.join(msg_str.split()[0:-1]).strip()
                msg_line = '{}\n'.format(info_all)
        else:
            # Best move can be None because engine dies
            try:
                best_move = chess.Move.from_uci(msg.split()[1])
            except Exception:
                sg.Popup('Engine error, it sent a {} bestmove.\n'.format(
                    best_move) + 'Back to Neutral mode, it is better to '
                                 'change engine {}.'.format(
                    self.opp_id_name), icon='Icon/pecg.png', title=BOX_TITLE)

        return best_move

    @staticmethod
    def get_tag_date():

        return datetime.today().strftime('%Y.%m.%d')

    def init_game(self):

        self.game = chess.pgn.Game()
        self.node = None
        self.game.headers['Event'] = INIT_PGN_TAG['Event']
        self.game.headers['Date'] = self.get_tag_date()
        self.game.headers['White'] = INIT_PGN_TAG['White']
        self.game.headers['Black'] = INIT_PGN_TAG['Black']

    def set_new_game(self):

        old_event = self.game.headers['Event']
        old_white = self.game.headers['White']
        old_black = self.game.headers['Black']

        # Define a game object for saving game in pgn format
        self.game = chess.pgn.Game()

        self.game.headers['Event'] = old_event
        self.game.headers['Date'] = self.get_tag_date()
        self.game.headers['White'] = old_white
        self.game.headers['Black'] = old_black

    @staticmethod
    def clear_elements(window):

        window.FindElement('_movelist_').Update(disabled=False)
        window.FindElement('_movelist_').Update('', disabled=True)
        window.FindElement('comment_k').Update('')
        window.Element('w_elapse_k').Update('')
        window.Element('b_elapse_k').Update('')

    def update_labels_and_game_tags(self, window, human='Human'):

        engine_id = self.opp_id_name
        if self.is_user_white:
            window.FindElement('_White_').Update(human)
            window.FindElement('_Black_').Update("AI")
            self.game.headers['White'] = human
            self.game.headers['Black'] = engine_id
        else:
            window.FindElement('_White_').Update("AI")
            window.FindElement('_Black_').Update(human)
            self.game.headers['White'] = engine_id
            self.game.headers['Black'] = human

    def fen_to_psg_board(self, window):

        psgboard = []
        pc_locations = self.fen.split()[0]

        board = chess.BaseBoard(pc_locations)
        old_r = None

        for s in chess.SQUARES:
            r = chess.square_rank(s)

            if old_r is None:
                piece_r = []
            elif old_r != r:
                psgboard.append(piece_r)
                piece_r = []
            elif s == 63:
                psgboard.append(piece_r)

            try:
                pc = board.piece_at(s ^ 56)
            except Exception:
                pc = None

            if pc is not None:
                pt = pc.piece_type
                c = pc.color
                if c:
                    if pt == chess.PAWN:
                        piece_r.append(PAWNW)
                    elif pt == chess.KNIGHT:
                        piece_r.append(KNIGHTW)
                    elif pt == chess.BISHOP:
                        piece_r.append(BISHOPW)
                    elif pt == chess.ROOK:
                        piece_r.append(ROOKW)
                    elif pt == chess.QUEEN:
                        piece_r.append(QUEENW)
                    elif pt == chess.KING:
                        piece_r.append(KINGW)
                else:
                    if pt == chess.PAWN:
                        piece_r.append(PAWNB)
                    elif pt == chess.KNIGHT:
                        piece_r.append(KNIGHTB)
                    elif pt == chess.BISHOP:
                        piece_r.append(BISHOPB)
                    elif pt == chess.ROOK:
                        piece_r.append(ROOKB)
                    elif pt == chess.QUEEN:
                        piece_r.append(QUEENB)
                    elif pt == chess.KING:
                        piece_r.append(KINGB)

            else:
                piece_r.append(BLANK)

            old_r = r

        self.psg_board = psgboard
        self.redraw_board(window)

    def change_square_color(self, window, row, col):

        btn_sq = window.FindElement(key=(row, col))
        is_dark_square = True if (row + col) % 2 else False
        bd_sq_color = self.move_sq_dark_color if is_dark_square else \
            self.move_sq_light_color
        btn_sq.Update(button_color=('white', bd_sq_color))

    def relative_row(self, s, stm):
        return 7 - self.get_row(s) if stm else self.get_row(s)

    @staticmethod
    def get_row(s):
        return 7 - chess.square_rank(s)

    @staticmethod
    def get_col(s):
        return chess.square_file(s)

    def redraw_board(self, window):

        for i in range(8):
            for j in range(8):
                color = self.sq_dark_color if (i + j) % 2 else \
                    self.sq_light_color
                piece_image = images[self.psg_board[i][j]]
                elem = window.FindElement(key=(i, j))
                elem.Update(button_color=('green', color),
                            image_filename=piece_image, )

    def render_square(self, image, key, location):

        if (location[0] + location[1]) % 2:
            color = self.sq_dark_color  # Dark square
        else:
            color = self.sq_light_color
        return sg.RButton('', image_filename=image, size=(1, 1),
                          border_width=0, button_color=('white', color),
                          pad=(0, 0), key=key)

    def select_promotion_piece(self, stm):

        piece = None
        board_layout, row = [], []

        psg_promote_board = copy.deepcopy(white_init_promote_board) if stm \
            else copy.deepcopy(black_init_promote_board)

        for i in range(1):
            for j in range(4):
                piece_image = images[psg_promote_board[i][j]]
                row.append(self.render_square(piece_image, key=(i, j),
                                              location=(i, j)))

            board_layout.append(row)

        promo_window = sg.Window('{}'.format(APP_NAME),
                                 board_layout,
                                 default_button_element_size=(12, 1),
                                 auto_size_buttons=False,
                                 icon='Icon/pecg.png')

        while True:
            button, value = promo_window.Read(timeout=0)
            if button is None:
                break
            if type(button) is tuple:
                move_from = button
                fr_row, fr_col = move_from
                piece = psg_promote_board[fr_row][fr_col]
                break
        promo_window.Close()

        return piece

    def update_rook(self, window, move):

        if move == 'e1g1':
            fr = chess.H1
            to = chess.F1
            pc = ROOKW
        elif move == 'e1c1':
            fr = chess.A1
            to = chess.D1
            pc = ROOKW
        elif move == 'e8g8':
            fr = chess.H8
            to = chess.F8
            pc = ROOKB
        elif move == 'e8c8':
            fr = chess.A8
            to = chess.D8
            pc = ROOKB

        self.psg_board[self.get_row(fr)][self.get_col(fr)] = BLANK
        self.psg_board[self.get_row(to)][self.get_col(to)] = pc
        self.redraw_board(window)

    def update_ep(self, window, move, stm):

        to = move.to_square
        if stm:
            capture_sq = to - 8
        else:
            capture_sq = to + 8

        self.psg_board[self.get_row(capture_sq)][self.get_col(capture_sq)] = BLANK
        self.redraw_board(window)

    def get_promo_piece(self, move, stm, human):

        if human:
            psg_promo = self.select_promotion_piece(stm)

            if psg_promo is None:
                psg_promo = QUEENW if stm else QUEENB

            pyc_promo = promote_psg_to_pyc[psg_promo]
        else:
            pyc_promo = move.promotion
            if stm:
                if pyc_promo == chess.QUEEN:
                    psg_promo = QUEENW
                elif pyc_promo == chess.ROOK:
                    psg_promo = ROOKW
                elif pyc_promo == chess.BISHOP:
                    psg_promo = BISHOPW
                elif pyc_promo == chess.KNIGHT:
                    psg_promo = KNIGHTW
            else:
                if pyc_promo == chess.QUEEN:
                    psg_promo = QUEENB
                elif pyc_promo == chess.ROOK:
                    psg_promo = ROOKB
                elif pyc_promo == chess.BISHOP:
                    psg_promo = BISHOPB
                elif pyc_promo == chess.KNIGHT:
                    psg_promo = KNIGHTB

        return pyc_promo, psg_promo

    def set_depth_limit(self):

        user_depth = sg.PopupGetText(
            'Current depth is {}\n\nInput depth [{} to {}]'.format(
                self.max_depth, MIN_DEPTH, MAX_DEPTH), title=BOX_TITLE,
            icon='Icon/pecg.png')

        try:
            user_depth = int(user_depth)
        except Exception:
            user_depth = self.max_depth

        self.max_depth = min(MAX_DEPTH, max(MIN_DEPTH, user_depth))

    def define_timer(self, window, name='human'):

        if name == 'human':
            timer = Timer(self.human_tc_type, self.human_base_time_ms,
                          self.human_inc_time_ms, self.human_period_moves)
        else:
            timer = Timer(self.engine_tc_type, self.engine_base_time_ms,
                          self.engine_inc_time_ms, self.engine_period_moves)
        return timer

    def play_game(self, window, x, board):

        window.FindElement('_movelist_').Update(disabled=False)
        window.FindElement('_movelist_').Update('', disabled=True)

        is_human_stm = True if self.is_user_white else False

        move_state = 0
        move_from, move_to = None, None
        is_new_game, is_exit_game, is_exit_app = False, False, False

        # Do not play immediately when stm is computer
        is_engine_ready = True if is_human_stm else False

        # For saving game
        move_cnt = 0

        is_user_resigns = False
        is_user_wins = False
        is_user_draws = False
        is_search_stop_for_exit = False
        is_search_stop_for_new_game = False
        is_search_stop_for_neutral = False
        is_hide_search_info = True

        # Init timer
        human_timer = self.define_timer(window)
        engine_timer = self.define_timer(window, 'engine')

        # Game loop
        global index, active, kkk, moves
        var = 1
        contor = 1
        local_var = 2

        while not board.is_game_over(claim_draw=True):

            def loadgame2(path, game):
                path = Path(path)
                vec = []
                for x in path.glob("*.txt"):
                    nr = re.search("[0-9]+", x.stem)
                    if str(game) == str(nr.group()):
                        if "fen" in str(x):
                            with open(x, "r") as fd:
                                content = fd.readlines()
                                for a in content:
                                    vec.append(a.strip("\n"))
                        if "pgn" in str(x):
                            with open(x, "r") as fd:
                                ceva = fd.read()
                                ceva = re.sub("[0-9]+\.", "", ceva)
                                moves = re.findall("[-/+#0-9a-zA-z]+", ceva)
                return vec, moves

            move_list2, moves2 = loadgame2(r"chess", game)
            last = moves2[len(moves2) - 1]
            antelast = moves2[len(moves2) - 2]
            var += 1

            if last == "1/2-1/2" and var == len(moves2) + 1:
                BOX_TITLE = "Draw"
                sg.Popup('Draw', title=BOX_TITLE, icon='Icon/pecg.png')
                window.FindElement('_White_').Update("Human")
                window.FindElement('_Black_').Update("AI")
                break
            if antelast == '1' and last == '0' and var == len(moves2):
                BOX_TITLE = "Player 1 won"
                sg.Popup('Player 1 won!', title=BOX_TITLE, icon='Icon/pecg.png')
                window.FindElement('_White_').Update("Human")
                window.FindElement('_Black_').Update("AI")
                break
            if antelast == '0' and last == '1' and var == len(moves2):
                BOX_TITLE = "Player 2 won"
                sg.Popup('Player 2 won!', title=BOX_TITLE, icon='Icon/pecg.png')
                window.FindElement('_White_').Update("Human")
                window.FindElement('_Black_').Update("AI")
                break

            moved_piece = None
            # Mode: Play, Stm: computer (first move), Allow user to change settings.
            # User can start the engine by Engine->Go.
            if not is_engine_ready:
                window.FindElement('_gamestatus_').Update(
                    'Mode     Play')
                while True:
                    button, value = window.Read(timeout=100)

                    # Mode: Play, Stm: computer (first move)
                    if button == 'New::new_game_k':
                        is_new_game = True
                        break

                    # Mode: Play, Stm: Computer first move
                    if button == 'Reset':
                        is_exit_game = True
                        index = 0
                        kkk = 0
                        active = False
                        window.FindElement('_White_').Update("Human")
                        window.FindElement('_Black_').Update("AI")
                        break

                    if button == 'Exit':
                        is_exit_app = True
                        window.Close()
                        sys.exit(0)
                        break

                    if button == 'Make move' and not active:
                        is_engine_ready = True
                        break

                    if button is None:
                        is_exit_app = True
                        break

                    if button == 'Auto' or active:
                        try:
                            if board.turn:
                                print('black to move')
                            else:
                                print('white to move')
                            maxeval = -9999
                            max_pos = moves[index]
                            for el in board.legal_moves:
                                info = engine.analyse(board, chess.engine.Limit(time=0.1), root_moves=[el])
                                t = str(info["score"])
                                if t.startswith('#'):
                                    t = str(t).replace('#', '')
                                if board.san(el) == moves[index]:
                                    aux = round(int(t)/100.,2)
                                if round(int(t)/100.,2) > maxeval:
                                    maxeval = round(int(t)/100.,2)
                                    max_pos = board.san(el)
                            self.fen = move_list[index]
                            self.set_new_game()
                            board = chess.Board(self.fen)
                        except Exception:
                            continue
                        absolut = abs(maxeval - aux)
                        self.fen_to_psg_board(window)
                        print('scorul maxim = ',maxeval)
                        print('pozitia maxima = ',max_pos)
                        print('scor book = ', aux)
                        print("absolut= ", absolut )
                        print("*"*30)
                        dct_neg = {
                            1: str(kkk // 2 + 1) + ". There is a way better move on:\t" + str(max_pos) + "\n",
                            2: str(kkk // 2 + 1) + ". Moving to\t" + str(
                                max_pos) + " would have increased it's winning chance\n",
                            3: str(kkk // 2 + 1) + ". A way better move would have been on \t" + str(
                                max_pos) + "\n"}

                        dct_pos = {
                            1: str(kkk // 2 + 1) + ". This was the best possible move!\n",
                            2: str(kkk // 2 + 1) + ". After that move he surely will win!\n",
                            3: str(kkk // 2 + 1) + ". Amazing move!\n"}

                        nr = random.randint(1, 3)
                        if (maxeval == aux):
                            window.FindElement("comment_k").Update(dct_pos[nr], append=True)
                        elif absolut >= 0.2:
                            window.FindElement("comment_k").Update(dct_neg[nr], append=True)

                        if kkk < len(moves):
                            if contor % 2 == 0:
                                window.FindElement('_movelist_').Update(str(local_var) + "." + str(moves[kkk]) + " ",
                                                                        append=True)
                                local_var += 1
                            else:
                                window.FindElement('_movelist_').Update(str(moves[kkk]) + " ", append=True)
                            contor += 1
                            kkk += 1

                        if not self.is_user_white and not board.turn:
                            is_human_stm = True
                            window.FindElement('_gamestatus_').Update(
                                'Mode     Play')

                        elif not self.is_user_white and board.turn:
                            is_human_stm = False
                            window.FindElement('_gamestatus_').Update(
                                'Mode     Play')

                        is_engine_ready = True if is_human_stm else False

                        self.game.headers['FEN'] = self.fen
                        time.sleep(0.3)
                        index += 1
                        if index >= len(move_list):
                            active = False
                            index = 0
                            if kkk < len(moves):
                                window.FindElement('_movelist_').Update(str(moves[kkk]) + " ", append=True)
                            kkk = 0
                        break

                if is_exit_app or is_exit_game or is_new_game:
                    break

            # If side to move is human
            if is_human_stm:
                move_state = 0

                while True:
                    button, value = window.Read(timeout=100)

                    # Update elapse box in m:s format
                    elapse_str = self.get_time_mm_ss_ms(human_timer.elapse)
                    k = 'w_elapse_k'
                    if not self.is_user_white:
                        k = 'b_elapse_k'
                    window.Element(k).Update(elapse_str)
                    human_timer.elapse += 100

                    if not is_human_stm:
                        break

                    if button is None:
                        is_exit_app = True
                        break

                    if button == 'Exit' or is_search_stop_for_exit:
                        is_exit_app = True
                        window.Close()
                        sys.exit(0)
                        break

                    # Mode: Play, Stm: User
                    if button == 'Reset' or is_search_stop_for_neutral:
                        is_exit_game = True
                        index = 0
                        kkk = 0
                        active = False
                        window.FindElement('_White_').Update("Human")
                        window.FindElement('_Black_').Update("AI")
                        self.clear_elements(window)
                        break

                    # Mode: Play, stm: User
                    if button == 'Make move' and not active:
                        if is_human_stm:
                            is_human_stm = False
                        else:
                            is_human_stm = True
                        is_engine_ready = True
                        window.FindElement('_gamestatus_').Update(
                            'Mode     Play, Engine is thinking ...')
                        break

                    # Mode: Play, stm: User
                    if button == 'Auto' or active:
                        if game == 1:
                            window.FindElement('_White_').Update("Garry Kasparov")
                            window.FindElement('_Black_').Update("The World")
                        if game == 5:
                            window.FindElement('_White_').Update("Magnus Carlsen")
                            window.FindElement('_Black_').Update("Fabiano Caruana")
                        if game == 6:
                            window.FindElement('_White_').Update("Fabiano Caruana")
                            window.FindElement('_Black_').Update("Magnus Carlsen")
                        if game == 7:
                            window.FindElement('_White_').Update("Magnus Carlsen")
                            window.FindElement('_Black_').Update("Sergey Karjakin")
                        if game == 8:
                            window.FindElement('_White_').Update("Sergey Karjakin")
                            window.FindElement('_Black_').Update("Magnus Carlsen")
                        if game == 9:
                            window.FindElement('_White_').Update("Vladimir Kramnik")
                            window.FindElement('_Black_').Update("Peter Svidler")
                        window.Element('w_elapse_k').Update('   -')
                        window.Element('b_elapse_k').Update('   -')
                        active = True
                        try:
                            self.fen = move_list[index]
                            self.set_new_game()
                            board = chess.Board(self.fen)
                        except Exception:
                            continue

                        self.fen_to_psg_board(window)
                        window.FindElement('_movelist_').Update("1.", append=True)
                        window.FindElement('_movelist_').Update(str(moves[kkk]) + " ", append=True)

                        # dct_pos = {
                        #     1: str(kkk // 2 + 1) + ". There is a way better move on:\t" + str(max_pos) + "\n",
                        #     2: str(kkk // 2 + 1) + ". Moving to:\t" + str(
                        #         max_pos) + " would have increased it's winning chance\n",
                        #     3: str(kkk // 2 + 1) + ". A way better move would have been on:\t" + str(
                        #         max_pos) + "\n"}
                        #
                        # dct_neg = {
                        #     1: str(kkk // 2 + 1) + ". This was the best possible move!\n",
                        #     2: str(kkk // 2 + 1) + ". After that move he surely will win!\n",
                        #     3: str(kkk // 2 + 1) + ". Amazing move!\n"}
                        #
                        # nr = random.randint(1, 3)
                        # if (maxeval - aux >= 1):
                        #     window.FindElement("comment_k").Update(dct_pos[nr], append=True)
                        # else:
                        #     window.FindElement("comment_k").Update(dct_neg[nr], append=True)
                        # kkk += 1

                        is_human_stm = True if board.turn else False
                        is_engine_ready = True if is_human_stm else False

                        window.FindElement('_gamestatus_').Update(
                            'Mode     Play, side: {}'.format(
                                'white' if board.turn else 'black'))
                        local = 1
                        self.game.headers['FEN'] = self.fen
                        time.sleep(0.3)
                        index += 1
                        if index >= len(move_list):
                            active = False
                            index = 0
                            if kkk < len(moves):
                                window.FindElement('_movelist_').Update(str(moves[kkk]) + " ", append=True)
                            kkk = 0
                        break

                    # Mode: Play, stm: User, user starts moving
                    if type(button) is tuple:
                        if move_state == 0:
                            move_from = button
                            fr_row, fr_col = move_from
                            piece = self.psg_board[fr_row][fr_col]

                            self.change_square_color(window, fr_row, fr_col)

                            move_state = 1
                            moved_piece = board.piece_type_at(chess.square(fr_col, 7 - fr_row))  # Pawn=1

                        elif move_state == 1:
                            is_promote = False
                            move_to = button
                            to_row, to_col = move_to
                            button_square = window.FindElement(key=(fr_row, fr_col))

                            if move_to == move_from:
                                color = self.sq_dark_color if (to_row + to_col) % 2 else self.sq_light_color

                                button_square.Update(button_color=('white', color))
                                move_state = 0
                                continue

                            user_move = None

                            fr_row, fr_col = move_from
                            fr_sq = chess.square(fr_col, 7 - fr_row)
                            to_sq = chess.square(to_col, 7 - to_row)

                            if self.relative_row(to_sq, board.turn) == RANK_8 and \
                                    moved_piece == chess.PAWN:
                                is_promote = True
                                pyc_promo, psg_promo = self.get_promo_piece(
                                    user_move, board.turn, True)
                                user_move = chess.Move(fr_sq, to_sq, promotion=pyc_promo)
                            else:
                                user_move = chess.Move(fr_sq, to_sq)

                            if user_move in board.legal_moves:
                                if board.is_castling(user_move):
                                    self.update_rook(window, str(user_move))

                                elif board.is_en_passant(user_move):
                                    self.update_ep(user_move, board.turn)

                                self.psg_board[move_from[0]][move_from[1]] = BLANK

                                if is_promote:
                                    self.psg_board[to_row][to_col] = psg_promo
                                else:
                                    self.psg_board[to_row][to_col] = piece

                                self.redraw_board(window)

                                board.push(user_move)
                                move_cnt += 1

                                human_timer.update_base()

                                time_left = human_timer.base
                                user_comment = value['comment_k']
                                self.update_game(move_cnt, user_move, time_left, user_comment)

                                window.FindElement('_movelist_').Update(disabled=False)
                                window.FindElement('_movelist_').Update('')
                                window.FindElement('_movelist_').Update(
                                    self.game.variations[0], append=True, disabled=True)

                                self.change_square_color(window, fr_row, fr_col)
                                self.change_square_color(window, to_row, to_col)

                                is_human_stm = not is_human_stm

                                k1 = 'w_elapse_k'
                                k2 = 'w_base_time_k'
                                if not self.is_user_white:
                                    k1 = 'b_elapse_k'
                                    k2 = 'b_base_time_k'

                                elapse_str = self.get_time_mm_ss_ms(
                                    human_timer.elapse)
                                window.Element(k1).Update(elapse_str)

                            else:
                                move_state = 0
                                color = self.sq_dark_color \
                                    if (move_from[0] + move_from[1]) % 2 else self.sq_light_color

                                button_square.Update(button_color=('white', color))
                                continue

                if is_new_game or is_exit_game or is_exit_app or \
                        is_user_resigns or is_user_wins or is_user_draws:
                    break

            elif not is_human_stm and is_engine_ready:
                is_promote = False
                best_move = None
                is_book_from_gui = True

                if best_move is None:
                    search = RunEngine(self.queue, self.engine_config_file,
                                       self.opp_path_and_file, self.opp_id_name,
                                       self.max_depth, engine_timer.base,
                                       engine_timer.inc,
                                       tc_type=engine_timer.tc_type,
                                       period_moves=board.fullmove_number)
                    search.get_board(board)
                    search.daemon = True
                    search.start()
                    window.FindElement('_gamestatus_').Update(
                        'Mode     Play, Engine is thinking ...')

                    while True:
                        button, value = window.Read(timeout=100)
                        elapse_str = self.get_time_mm_ss_ms(engine_timer.elapse)
                        k = 'b_elapse_k'
                        if not self.is_user_white:
                            k = 'w_elapse_k'
                        window.Element(k).Update(elapse_str)
                        engine_timer.elapse += 100

                        # Exit app while engine is thinking
                        if button == 'Exit':
                            search.stop()
                            is_search_stop_for_exit = True
                            window.Close()
                            sys.exit(0)

                        # Forced engine to move now
                        if button == 'Move Now':
                            search.stop()

                        # Mode: Play, Computer is thinking
                        if button == 'Reset':
                            search.stop()
                            index = 0
                            kkk = 0
                            active = False
                            is_search_stop_for_neutral = True
                            window.FindElement('_White_').Update("Human")
                            window.FindElement('_Black_').Update("AI")

                        # Get the engine search info and display it in GUI text boxes
                        try:
                            msg = self.queue.get_nowait()
                        except Exception:
                            continue

                        msg_str = str(msg)
                        best_move = self.update_text_box(window, msg, is_hide_search_info)
                        if 'bestmove' in msg_str:
                            break

                    search.join()
                    search.quit_engine()
                    is_book_from_gui = False

                # If engine failed to send a legal move
                if best_move is None:
                    break

                # Update board with computer move
                move_str = str(best_move)
                fr_col = ord(move_str[0]) - ord('a')
                fr_row = 8 - int(move_str[1])
                to_col = ord(move_str[2]) - ord('a')
                to_row = 8 - int(move_str[3])

                piece = self.psg_board[fr_row][fr_col]
                self.psg_board[fr_row][fr_col] = BLANK

                # Update rook location if this is a castle move
                if board.is_castling(best_move):
                    self.update_rook(window, move_str)

                # Update board if e.p capture
                elif board.is_en_passant(best_move):
                    self.update_ep(best_move, board.turn)

                # Update board if move is a promotion
                elif best_move.promotion is not None:
                    is_promote = True
                    _, psg_promo = self.get_promo_piece(best_move, board.turn, False)

                # Update board to_square if move is a promotion
                if is_promote:
                    self.psg_board[to_row][to_col] = psg_promo
                else:
                    self.psg_board[to_row][to_col] = piece

                self.redraw_board(window)

                board.push(best_move)
                move_cnt += 1

                # Update timer
                engine_timer.update_base()

                time_left = engine_timer.base
                if is_book_from_gui:
                    engine_comment = 'book'
                else:
                    engine_comment = ''
                self.update_game(move_cnt, best_move, time_left, engine_comment)

                window.FindElement('_movelist_').Update(disabled=False)
                window.FindElement('_movelist_').Update('')
                window.FindElement('_movelist_').Update(
                    self.game.variations[0], append=True, disabled=True)

                self.change_square_color(window, fr_row, fr_col)
                self.change_square_color(window, to_row, to_col)

                is_human_stm = not is_human_stm

                k1 = 'b_elapse_k'
                k2 = 'b_base_time_k'
                if not self.is_user_white:
                    k1 = 'w_elapse_k'
                    k2 = 'w_base_time_k'

                elapse_str = self.get_time_mm_ss_ms(engine_timer.elapse)
                window.Element(k1).Update(elapse_str)

                window.FindElement('_gamestatus_').Update('Mode     Play')

        if is_user_resigns:
            self.game.headers['Result'] = '0-1' if self.is_user_white else '1-0'
            self.game.headers['Termination'] = '{} resigns'.format(
                'white' if self.is_user_white else 'black')
        elif is_user_wins:
            self.game.headers['Result'] = '1-0' if self.is_user_white else '0-1'
            self.game.headers['Termination'] = 'Adjudication'
        elif is_user_draws:
            self.game.headers['Result'] = '1/2-1/2'
            self.game.headers['Termination'] = 'Adjudication'
        else:
            self.game.headers['Result'] = board.result(claim_draw=True)

        base_h = int(self.human_base_time_ms / 1000)
        inc_h = int(self.human_inc_time_ms / 1000)
        base_e = int(self.engine_base_time_ms / 1000)
        inc_e = int(self.engine_inc_time_ms / 1000)

        if self.is_user_white:
            if self.human_tc_type == 'fischer':
                self.game.headers['WhiteTimeControl'] = str(base_h) + '+' + \
                                                        str(inc_h)
            elif self.human_tc_type == 'delay':
                self.game.headers['WhiteTimeControl'] = str(base_h) + '-' + \
                                                        str(inc_h)
            if self.engine_tc_type == 'fischer':
                self.game.headers['BlackTimeControl'] = str(base_e) + '+' + \
                                                        str(inc_e)
            elif self.engine_tc_type == 'timepermove':
                self.game.headers['BlackTimeControl'] = str(1) + '/' + str(base_e)
        else:
            if self.human_tc_type == 'fischer':
                self.game.headers['BlackTimeControl'] = str(base_h) + '+' + \
                                                        str(inc_h)
            elif self.human_tc_type == 'delay':
                self.game.headers['BlackTimeControl'] = str(base_h) + '-' + \
                                                        str(inc_h)
            if self.engine_tc_type == 'fischer':
                self.game.headers['WhiteTimeControl'] = str(base_e) + '+' + \
                                                        str(inc_e)
            elif self.engine_tc_type == 'timepermove':
                self.game.headers['WhiteTimeControl'] = str(1) + '/' + str(base_e)
        self.save_game()

        if board.is_game_over(claim_draw=True):
            BOX_TITLE = "Game Over"
            sg.Popup('Game Over!', title=BOX_TITLE, icon='Icon/pecg.png')

        if is_exit_app:
            window.Close()
            sys.exit(0)

        self.clear_elements(window)

        return False if is_exit_game else is_new_game

    def save_game(self):

        with open(self.pecg_auto_save_game, mode='a+') as f:
            f.write('{}\n\n'.format(self.game))

    def get_engines(self):

        engine_list = []
        engine_path = Path('Engines')
        files = os.listdir(engine_path)
        for file in files:
            if not file.endswith('.gz') and not file.endswith('.dll') \
                    and not file.endswith('.bin') \
                    and not file.endswith('.dat'):
                engine_list.append(file)

        return engine_list

    def create_board(self, is_user_white=True):

        file_char_name = 'abcdefgh'
        self.psg_board = copy.deepcopy(initial_board)

        board_layout = []

        if is_user_white:
            # Save the board with black at the top
            start = 0
            end = 8
            step = 1
        else:
            start = 7
            end = -1
            step = -1
            file_char_name = file_char_name[::-1]

        for i in range(start, end, step):
            # Row numbers at left of board is blank
            row = []
            for j in range(start, end, step):
                piece_image = images[self.psg_board[i][j]]
                row.append(self.render_square(piece_image, key=(i, j), location=(i, j)))
            board_layout.append(row)

        return board_layout

    def build_main_layout(self, is_user_white=True):

        sg.ChangeLookAndFeel(self.gui_theme)
        sg.SetOptions(margins=(0, 0), border_width=1)

        # Define board
        board_layout = self.create_board(is_user_white)
        alg_fundation_numbers = [[sg.Text(' ', size=(0, 1), font=('Consolas', 7))],
                                 [sg.Text('1', size=(0, 3), font=('Consolas', 11))],
                                 [sg.Text('2', size=(0, 3), font=('Consolas', 11))],
                                 [sg.Text('3', size=(0, 3), font=('Consolas', 11))],
                                 [sg.Text('4', size=(0, 2), font=('Consolas', 11))],
                                 [sg.Text('5', size=(0, 3), font=('Consolas', 11))],
                                 [sg.Text('6', size=(0, 2), font=('Consolas', 11))],
                                 [sg.Text('7', size=(0, 3), font=('Consolas', 11))],
                                 [sg.Text('8', size=(0, 3), font=('Consolas', 11))]]
        board_controls = [
            [sg.Text('Mode       Start playing!', size=(36, 1), font=('Consolas', 10), key='_gamestatus_')],
            [sg.Text('White', size=(7, 1), font=('Consolas', 10)),
             sg.Text('Human', font=('Consolas', 10), key='_White_',
                     size=(24, 1), relief='sunken'),
             sg.Text('', font=('Consolas', 10), key='w_elapse_k', size=(7, 1),
                     relief='sunken')
             ],
            [sg.Text('Black', size=(7, 1), font=('Consolas', 10)),
             sg.Text('Computer', font=('Consolas', 10), key='_Black_',
                     size=(24, 1), relief='sunken'),
             sg.Text('', font=('Consolas', 10), key='b_elapse_k', size=(7, 1),
                     relief='sunken')
             ],
            [sg.Text('Move list', size=(16, 1), font=('Consolas', 10))],
            [sg.Multiline('', do_not_clear=True, autoscroll=True, size=(52, 10),
                          font=('Consolas', 10), key='_movelist_', disabled=True)],

            [sg.Text('Comment', size=(7, 1), font=('Consolas', 10))],
            [sg.Multiline('', do_not_clear=True, autoscroll=True, size=(52, 14),
                          font=('Consolas', 10), key='comment_k', disabled=True)]
        ]

        board_tab = [[sg.Column(board_layout)],
                     [sg.Text(' ', size=(2, 1), font=('Consolas', 8)),
                      sg.Text('a', size=(5, 1), font=('Consolas', 12)),
                      sg.Text('b', size=(5, 1), font=('Consolas', 12)),
                      sg.Text('c', size=(5, 1), font=('Consolas', 12)),
                      sg.Text('d', size=(5, 1), font=('Consolas', 12)),
                      sg.Text('e', size=(5, 1), font=('Consolas', 12)),
                      sg.Text('f', size=(5, 1), font=('Consolas', 12)),
                      sg.Text('g', size=(5, 1), font=('Consolas', 12)),
                      sg.Text('h', size=(5, 1), font=('Consolas', 12))]
                     ]
        self.menu_elem = sg.Menu(menu_def_neutral, tearoff=False)

        layout = [
            [self.menu_elem],
            [sg.Column(alg_fundation_numbers), sg.Column(board_tab), sg.Column(board_controls)]
        ]

        return layout

    def main_loop(self):

        layout = self.build_main_layout(True)

        window = sg.Window('{}'.format(APP_NAME),
                           layout, default_button_element_size=(12, 1),
                           auto_size_buttons=False, icon='Icon/pecg.png')

        self.check_engine_config_file()

        self.engine_id_name_list = self.get_engine_id_name_list()

        engine_id_name = self.opp_id_name = self.engine_id_name_list[0]
        self.opp_file, self.opp_path_and_file = self.get_engine_file(
            engine_id_name)

        self.adviser_id_name = self.engine_id_name_list[1] \
            if len(self.engine_id_name_list) >= 2 \
            else self.engine_id_name_list[0]
        self.adviser_file, self.adviser_path_and_file = self.get_engine_file(
            self.adviser_id_name)

        self.init_game()

        while True:
            button, value = window.Read(timeout=50)
            self.update_labels_and_game_tags(window, human=self.username)
            break

        while True:
            button, value = window.Read(timeout=50)

            if button == 'Exit':
                window.Close()
                sys.exit(0)
                break

            # Mode: Neutral
            if button is None:
                break

            # Mode: Neutral
            if button == 'Set Depth':
                self.set_depth_limit()
                continue

            def loadgame(path, game):
                path = Path(path)
                vec = []
                for x in path.glob("*.txt"):
                    nr = re.search("[0-9]+", x.stem)
                    if str(game) == str(nr.group()):
                        if "fen" in str(x):
                            with open(x, "r") as fd:
                                content = fd.readlines()
                                for a in content:
                                    vec.append(a.strip("\n"))
                        if "pgn" in str(x):
                            with open(x, "r") as fd:
                                ceva = fd.read()
                                ceva = re.sub("[0-9]+\.", "", ceva)
                                moves = re.findall("[-/+#0-9a-zA-z]+", ceva)
                return vec, moves

            # Mode: Neutral, Change theme
            if button in GUI_THEME:
                self.gui_theme = button
                window = self.create_new_window(window)
                continue

            if button in lista:
                global game, move_list, moves
                game = int(button[0])
                move_list, moves = loadgame(r"chess", game)
                continue

            # Mode: Neutral, Change board to gray
            if button == 'Gray::board_color_k':
                self.sq_light_color = '#D8D8D8'
                self.sq_dark_color = '#808080'
                self.move_sq_light_color = '#e0e0ad'
                self.move_sq_dark_color = '#999966'
                self.redraw_board(window)
                window = self.create_new_window(window)
                continue

            # Mode: Neutral, Change board to green
            if button == 'Green::board_color_k':
                self.sq_light_color = '#daf1e3'
                self.sq_dark_color = '#3a7859'
                self.move_sq_light_color = '#bae58f'
                self.move_sq_dark_color = '#6fbc55'
                self.redraw_board(window)
                window = self.create_new_window(window)
                continue

            # Mode: Neutral, Change board to blue
            if button == 'Blue::board_color_k':
                self.sq_light_color = '#b9d6e8'
                self.sq_dark_color = '#4790c0'
                self.move_sq_light_color = '#d2e4ba'
                self.move_sq_dark_color = '#91bc9c'
                self.redraw_board(window)
                window = self.create_new_window(window)
                continue

            # Mode: Neutral, Change board to brown, default
            if button == 'Brown::board_color_k':
                self.sq_light_color = '#F0D9B5'
                self.sq_dark_color = '#B58863'
                self.move_sq_light_color = '#E8E18E'
                self.move_sq_dark_color = '#B8AF4E'
                self.redraw_board(window)
                window = self.create_new_window(window)
                continue

            # Mode: Neutral
            if button == 'Play':
                # Change menu from Neutral to Play
                self.menu_elem.Update(menu_def_play)
                self.psg_board = copy.deepcopy(initial_board)
                board = chess.Board()

                while True:
                    button, value = window.Read(timeout=100)

                    window.FindElement('_gamestatus_').Update('Mode     Play')
                    window.FindElement('_movelist_').Update(disabled=False)
                    window.FindElement('_movelist_').Update('', disabled=True)

                    start_new_game = self.play_game(window, engine_id_name, board)
                    window.FindElement('_gamestatus_').Update('Mode     Start playing!')

                    self.psg_board = copy.deepcopy(initial_board)
                    self.redraw_board(window)
                    board = chess.Board()
                    self.set_new_game()

                    if not start_new_game:
                        break

                # Restore Neutral menu
                self.menu_elem.Update(menu_def_neutral)
                self.psg_board = copy.deepcopy(initial_board)
                board = chess.Board()
                self.set_new_game()
                continue

        window.Close()


def main():
    global engine
    engine = chess.engine.SimpleEngine.popen_uci('stockfish_10_x64.exe')
    global move_list, active, index

    active = False
    index = 0

    engine_config_file = 'pecg_engines.json'
    user_config_file = 'pecg_user.json'

    pecg_book = 'book/pecg_book.bin'
    book_from_computer_games = 'book/computer.bin'
    book_from_human_games = 'book/human.bin'

    is_use_gui_book = True
    is_random_book = True
    max_book_ply = 8
    theme = 'Topanga'

    pecg = EasyChessGui(theme, engine_config_file, user_config_file,
                        pecg_book, book_from_computer_games,
                        book_from_human_games, is_use_gui_book, is_random_book,
                        max_book_ply)
    pecg.main_loop()
    engine.quit()


if __name__ == "__main__":
    main()
