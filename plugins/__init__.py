from os import listdir
from os.path import isdir, join
from kernel.macro import Macro

from traceback import print_exc

ignored_plugins = (
        "mediator"
        )


def load_plugins(top, plugin_dir="plugins"):
    print("scanning plugins ... ", end="")
    loaded = []

    for plugin in listdir(plugin_dir):
        if plugin in ignored_plugins:
            continue

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

                        # FIXME: make a decision: who is responsible to register the Macros?

                        # if isinstance(top.namespace[item], Macro):
                            # top.namespace[item].register()

                    loaded.append(plugin)
                except Exception as err:
                    print_exc()

    print("%d plugins detected: %s" % (
        len(loaded),
        str(loaded)
        ))
