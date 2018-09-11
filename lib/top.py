import traceback

class Top:

    def __init__(self):
        self.namespace = {}

    def run(self):
        while True:
            command = input("holboost >>> ")
            try:
                exec(command, self.namespace)
            except Exception as err:
                traceback.print_exc()
