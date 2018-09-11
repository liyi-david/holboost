from http.server import BaseHTTPRequestHandler, HTTPServer
from formats.json import JsonFormat, JsonConvertError

import threading
import json


def CoqTaskHandlerFactory(top : 'Top'):
    # to generate CoqTaskHandlers with arguments

    class CoqTaskHandler(BaseHTTPRequestHandler):

        def do_POST(self):

            reply = {
                    "error" : True,
                    "msg"   : "unhandled api url %s" % self.path
                    }

            if self.path == "/prove":
                data = self.rfile.read(int(self.headers['content-length']))
                data = data.decode('utf8')

                try:
                    task = JsonFormat.import_task(data)
                    top.namespace['task'] = task

                    # do something ...
                    reply = {
                            "error"    : False,
                            "finished" : True,
                            "msg"      : "",
                            }

                except JsonConvertError as err:
                    reply = {
                            "error"    : True,
                            "msg"      : str(err)
                            }


            self.send_response(200)
            self.send_header('Content-type', 'text/json')
            self.end_headers()
            self.wfile.write(json.dumps(reply).encode('utf8'))

    return CoqTaskHandler



def run_coq_server(port=8081, top=None):
    print('start listening on port %d, press <Ctrl+c> to stop.' % port)
    http = HTTPServer(('', port), CoqTaskHandlerFactory(top))
    thread = threading.Thread(target = http.serve_forever)
    thread.daemon = True
    thread.start()
    return http

