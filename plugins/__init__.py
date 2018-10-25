from os import listdir
from os.path import isdir, join

from traceback import print_exc

plugin_dir = "plugins"

def load_plugins(top):
    print("scanning plugins ... ", end="")
    loaded = []

    for plugin in listdir(plugin_dir):
        if isdir(join(plugin_dir, plugin)):
            files = listdir(join(plugin_dir, plugin))
            if "__init__.py" in files:
                # this is a valid plugin!
                try:
                    mod = __import__(plugin_dir + "." + plugin, fromlist=['*'])
                    for item in dir(mod):
                        if item.startswith("__"):
                            continue

                        top.namespace[item] = getattr(mod, item)

                    loaded.append(plugin)
                except Exception as err:
                    print_exc()

    print("%d loaded." % len(loaded))
    top.print(loaded)
