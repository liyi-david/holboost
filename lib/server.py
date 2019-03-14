from http.server import BaseHTTPRequestHandler, HTTPServer
from urllib.parse import urlparse, parse_qs
from time import time
from sys import stdout

from interaction.commands import IdleCommand, ConnectCommand, DisconnectCommand, RunCommand
from kernel.environment import NamedEnvironment
from kernel.session import Session
from kernel.task import Task

import threading
import traceback
import cProfile

import json


threshold = 0.1


def CoqTaskHandlerFactory(top : 'Top', profile : bool):
    # to generate CoqTaskHandlers with arguments

    class CoqTaskHandler(BaseHTTPRequestHandler):

        def do_GET(self):

            top.debug("server", "GET request received.")
            data = parse_qs(urlparse(self.path).query)
            top.debug("server", "GET request received.")

            # data could be in form of { a : [b] ... }
            for key in data:
                if len(data[key]) == 1:
                    data[key] = data[key][0]

            req = {
                'client': 'browser',
                'session': None,
                'content': {
                    'constants': [],
                    'variables': [],
                    'mutinds': [],
                    'command': data
                    }
                }

            self.do_REQUEST(req)

        def do_POST(self):

            top.debug("server", "=" * 80)

            if self.client_address[0] in ('localhost', '127.0.0.1'):
                # when the request comes from localhost, we perfer reading the task
                # from a file on the disk
                tmp_filename = self.path[1:]
                with open(tmp_filename, 'r') as f:
                    data = f.read()
            else:
                # FIXME rfile.read could be extremely slow due to a signal-waiting issue
                # this is still not clear for me, but currently we only consider local
                # requests
                data = self.rfile.read(int(self.headers['content-length']))
                data = data.decode('utf8')

            t0 = time()

            # data pre-processing: from string to json
            parsed_data = json.loads(data)

            data_preprocessing_time = time() - t0
            if data_preprocessing_time > threshold:
                top.debug("server", "posted data size %d KB" % (len(data) / 1024))
                top.debug("server", "data pre-processing time cost: %.6f" % (time() - t0))

            top.namespace['__request__'] = parsed_data

            self.do_REQUEST(parsed_data)

        def do_REQUEST(self, parsed_data):
            reply = {
                    "error" : True,
                    "msg"   : "unhandled api url %s" % self.path
                    }

            try:
                t0 = time()

                session_id = None
                if 'session' in parsed_data:
                    session_id = parsed_data['session']

                top.debug("server", "session id " + str(session_id))
                task = Task.from_json(parsed_data['content'])

                task_importing_time = time() - t0

                if task_importing_time > threshold:
                    top.debug("server", "task importing time cost: %.6f" % task_importing_time)

                task.client = parsed_data['client']
                task.client_addr = self.client_address

                top.print(task)

                # merge buffered builtin declarations with the task
                # NOTE this feature has been moved to the ConnectCommand
                # if task.client in top.namespace['cache']:
                #     task.inherited_environment = top.namespace['cache'][task.client]
                if session_id is not None:
                    session = Session.get(session_id)
                    task.inherited_environment = session.task
                    session.task = task

                if profile and type(task.command) not in (IdleCommand, ConnectCommand, DisconnectCommand, RunCommand):
                    prof = cProfile.Profile()
                    result = prof.runcall(task.run, top)

                    # analyzing stats
                    top.print_profile(prof)
                else:
                    result = task.run(top)

                top.namespace['__result__'] = result

                if task.client not in top.namespace['cache']:
                    builtins = task.get_builtins()
                    if len(builtins.constants().values()) + len(builtins.mutinds().values()) > 0:
                        top.namespace['cache'][task.client] = builtins

                reply = {
                        "error"    : False,
                        "finished" : True,
                        "msg"      : "",
                        "feedback" : result,
                        "builtin_cached": (task.client in top.namespace['cache']),
                        }

                # top.debug("server", "response", reply)

            except json.JSONDecodeError as err:
                top.print(data[err.pos - 10:err.pos + 10])
                reply = {
                        "error"    : True,
                        "msg"      : "json decoding failes because %s. for further information please refer to the server log" % str(err)
                        }
            except Session.SessionNotFoundError as err:
                reply = {
                        "error"    : True,
                        "msg"      : "session lost"
                        }
            except Exception as err:
                top.print("Exception captured.")
                traceback.print_exc()

                reply = {
                        "error"    : True,
                        "msg"      : str(type(err).__name__) + " " + str(err)
                        }


            self.send_response(200)
            self.send_header('Content-type', 'text/json')
            self.end_headers()

            time_cost = time() - t0
            top.debug("server", "total task time cost : %.6f" % time_cost)

            self.wfile.write(json.dumps(reply).encode('utf8'))


        def log_message(self, format, *args):
            top.log_message(format % args)

    return CoqTaskHandler



def run_coq_server(port=8081, top=None, profile=False):
    print('start listening on port %d, press <Ctrl+c> to stop.' % port)
    http = HTTPServer(('', port), CoqTaskHandlerFactory(top, profile))
    thread = threading.Thread(target = http.serve_forever)
    thread.daemon = True
    thread.start()
    return http

