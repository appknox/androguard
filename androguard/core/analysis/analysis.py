from __future__ import print_function
from builtins import str
import re
import collections
import time
import warnings
from androguard.core.androconf import is_ascii_problem, \
    load_api_specific_resource_module
from androguard.core.bytecodes import dvm
import logging
from androguard.core import bytecode
import networkx as nx


log = logging.getLogger("androguard.analysis")

BasicOPCODES = []
for i in dvm.BRANCH_DVM_OPCODES:
    BasicOPCODES.append(re.compile(i))

# Flags used in :class:`ClassAnalysis`.
REF_NEW_INSTANCE = 0
REF_CLASS_USAGE = 1

ref_type = {0x22: REF_NEW_INSTANCE, 0x1c: REF_CLASS_USAGE}


TAINTED_LOCAL_VARIABLE = 0
TAINTED_FIELD = 1
TAINTED_STRING = 2
TAINTED_PACKAGE_CREATE = 0
TAINTED_PACKAGE_CALL = 1

TAINTED_PACKAGE = {
    TAINTED_PACKAGE_CREATE: "C",
    TAINTED_PACKAGE_CALL: "M"
}

TAINTED_PACKAGE_INTERNAL_CALL = 2
FIELD_ACCESS = {"R": 0, "W": 1}
PACKAGE_ACCESS = {TAINTED_PACKAGE_CREATE: 0,
                  TAINTED_PACKAGE_CALL: 1, TAINTED_PACKAGE_INTERNAL_CALL: 2}

DVM_FIELDS_ACCESS = {
    "iget": "R",
    "iget-wide": "R",
    "iget-object": "R",
    "iget-boolean": "R",
    "iget-byte": "R",
    "iget-char": "R",
    "iget-short": "R",

    "iput": "W",
    "iput-wide": "W",
    "iput-object": "W",
    "iput-boolean": "W",
    "iput-byte": "W",
    "iput-char": "W",
    "iput-short": "W",

    "sget": "R",
    "sget-wide": "R",
    "sget-object": "R",
    "sget-boolean": "R",
    "sget-byte": "R",
    "sget-char": "R",
    "sget-short": "R",

    "sput": "W",
    "sput-wide": "W",
    "sput-object": "W",
    "sput-boolean": "W",
    "sput-byte": "W",
    "sput-char": "W",
    "sput-short": "W",
}


class DVMBasicBlock(object):
    """
        A simple basic block of a dalvik method
    """

    def __init__(self, start, vm, method, context):
        self.__vm = vm
        self.method = method
        self.context = context

        self.last_length = 0
        self.nb_instructions = 0

        self.fathers = []
        self.childs = []

        self.start = start
        self.end = self.start

        self.special_ins = {}

        self.name = "%s-BB@0x%x" % (self.method.get_name(), self.start)
        self.exception_analysis = None

        self.notes = []

        self.__cached_instructions = None

        self.tainted_variables = self.context.get_tainted_variables()
        self.tainted_packages = self.context.get_tainted_packages()

    def get_notes(self):
        return self.notes

    def set_notes(self, value):
        self.notes = [value]

    def add_note(self, note):
        self.notes.append(note)

    def clear_notes(self):
        self.notes = []

    def get_instructions(self):
        """
        Get all instructions from a basic block.

        :rtype: Return all instructions in the current basic block
        """
        tmp_ins = []
        idx = 0
        for i in self.method.get_instructions():
            if self.start <= idx < self.end:
                yield i
            idx += i.get_length()

    def get_nb_instructions(self):
        return self.nb_instructions

    def get_method(self):
        return self.method

    def get_name(self):
        return "%s-BB@0x%x" % (self.method.get_name(), self.start)

    def get_start(self):
        return self.start

    def get_end(self):
        return self.end

    def get_last(self):
        return self.get_instructions()[-1]

    def get_next(self):
        """
            Get next basic blocks

            :rtype: a list of the next basic blocks
        """
        return self.childs

    def get_prev(self):
        """
            Get previous basic blocks

            :rtype: a list of the previous basic blocks
        """
        return self.fathers

    def set_fathers(self, f):
        self.fathers.append(f)

    def get_last_length(self):
        return self.last_length

    def set_childs(self, values):
        # print self, self.start, self.end, values
        if not values:
            next_block = self.context.get_basic_block(self.end + 1)
            if next_block is not None:
                self.childs.append((self.end - self.get_last_length(), self.end,
                                    next_block))
        else:
            for i in values:
                if i != -1:
                    next_block = self.context.get_basic_block(i)
                    if next_block is not None:
                        self.childs.append((self.end - self.get_last_length(),
                                            i, next_block))

        for c in self.childs:
            if c[2] is not None:
                c[2].set_fathers((c[1], c[0], self))

    def push(self, i):
        self.nb_instructions += 1
        idx = self.end
        self.last_length = i.get_length()
        self.end += self.last_length

        op_value = i.get_op_value()

        if (op_value >= 0x52 and op_value <= 0x6d):
                desc = self.__vm.get_cm_field(i.get_ref_kind())
                if self.tainted_variables is not None:
                    self.tainted_variables.push_info(
                        TAINTED_FIELD, desc,
                        DVM_FIELDS_ACCESS[i.get_name()][0], idx, self.method)

        # invoke
        elif (op_value >= 0x6e and op_value <= 0x72) or (
                op_value >= 0x74 and op_value <= 0x78):
            idx_meth = i.get_ref_kind()
            method_info = self.__vm.get_cm_method(idx_meth)
            if self.tainted_packages is not None:
                self.tainted_packages.push_info(
                    method_info[0], TAINTED_PACKAGE_CALL, idx, self.method,
                    idx_meth)

        # new_instance
        elif op_value == 0x22:
            idx_type = i.get_ref_kind()
            type_info = self.__vm.get_cm_type(idx_type)
            if self.tainted_packages is not None:
                self.tainted_packages.push_info(
                    type_info, TAINTED_PACKAGE_CREATE, idx, self.method, None)

        # const-string
        elif (op_value >= 0x1a and op_value <= 0x1b):
            string_name = self.__vm.get_cm_string(i.get_ref_kind())
            if self.tainted_variables is not None:
                self.tainted_variables.push_info(
                    TAINTED_STRING, string_name, "R", idx, self.method)

        elif op_value == 0x26 or (0x2b <= op_value <= 0x2c):
            code = self.method.get_code().get_bc()
            self.special_ins[idx] = code.get_ins_off(idx + i.get_ref_off() * 2)

    def get_special_ins(self, idx):
        """
            Return the associated instruction to a specific instruction (for example a packed/sparse switch)

            :param idx: the index of the instruction

            :rtype: None or an Instruction
        """
        if idx in self.special_ins:
            return self.special_ins[idx]
        else:
            return None

    def get_exception_analysis(self):
        return self.exception_analysis

    def set_exception_analysis(self, exception_analysis):
        self.exception_analysis = exception_analysis

    def show(self):
        print(self.get_name(), self.get_start(), self.get_end())


class PathVar(object):

    def __init__(self, access, idx, dst_idx, info_obj):
        self.access_flag = access
        self.idx = idx
        self.dst_idx = dst_idx
        self.info_obj = info_obj

    def get_var_info(self):
        return self.info_obj.get_info()

    def get_access_flag(self):
        return self.access_flag

    def get_src(self, cm):
        method = cm.get_method_ref(self.idx)
        return method.get_class_name(), method.get_name(), method.get_descriptor()

    def get_dst(self, cm):
        method = cm.get_method_ref(self.dst_idx)
        return method.get_class_name(), method.get_name(), method.get_descriptor()

    def get_idx(self):
        return self.idx


class TaintedVariable(object):

    def __init__(self, var, _type):
        self.var = var
        self.type = _type

        self.paths = {}
        self.__cache = []

    def get_type(self):
        return self.type

    def get_info(self):
        if self.type == TAINTED_FIELD:
            return [self.var[0], self.var[2], self.var[1]]
        return self.var

    def push(self, access, idx, ref):
        m_idx = ref.get_method_idx()

        if m_idx not in self.paths:
            self.paths[m_idx] = []

        self.paths[m_idx].append((access, idx))

    def get_paths_access(self, mode):
        for i in self.paths:
            for j in self.paths[i]:
                for k, v in self.paths[i][j]:
                    if k in mode:
                        yield i, j, k, v

    def get_paths(self):
        if self.__cache != []:
            return self.__cache

        for i in self.paths:
            for j in self.paths[i]:
                self.__cache.append([j, i])
                # yield j, i
        return self.__cache

    def get_paths_length(self):
        return len(self.paths)

    def show_paths(self, vm):
        show_PathVariable(vm, self.get_paths())


class TaintedVariables(object):

    def __init__(self, _vm):
        self.__vm = _vm
        self.__vars = {
            TAINTED_LOCAL_VARIABLE: {},
            TAINTED_FIELD: {},
            TAINTED_STRING: {},
        }

        self.__cache_field_by_method = {}
        self.__cache_string_by_method = {}

        self.AOSP_PERMISSIONS_MODULE = load_api_specific_resource_module(
            "aosp_permissions", self.__vm.get_api_version())
        self.API_PERMISSION_MAPPINGS_MODULE = load_api_specific_resource_module(
            "api_permission_mappings", self.__vm.get_api_version())

    # functions to get particulars elements
    def get_string(self, s):
        try:
            return self.__vars[TAINTED_STRING][s]
        except KeyError:
            return None

    def get_field(self, class_name, name, descriptor):
        key = class_name + descriptor + name

        try:
            return self.__vars[TAINTED_FIELD][key]
        except KeyError:
            return None

    def toPathVariable(self, obj):
        z = []
        for i in obj.get_paths():
            access, idx = i[0]
            m_idx = i[1]

            z.append(PathVar(access, idx, m_idx, obj))
        return z

    # permission functions
    def get_permissions_method(self, method):
        permissions = set()

        for f, f1 in self.get_fields():
            data = "%s-%s-%s" % (f.var[0], f.var[2], f.var[1])
            if data in list(
                    self.API_PERMISSION_MAPPINGS_MODULE[
                        "AOSP_PERMISSIONS_BY_FIELDS"].keys()):
                for path in f.get_paths():
                    #access, idx = path[0]
                    m_idx = path[1]
                    if m_idx == method.get_idx():
                        permissions.update(self.API_PERMISSION_MAPPINGS_MODULE[
                                           "AOSP_PERMISSIONS_BY_FIELDS"][data])

        return permissions

    def get_permissions(self, permissions_needed):
        """
            @param permissions_needed : a list of restricted permissions to get
                                        ([] returns all permissions)

            @rtype : a dictionnary of permissions' paths
        """
        permissions = {}

        pn = set(permissions_needed)
        if permissions_needed == []:
            pn = set(self.AOSP_PERMISSIONS_MODULE["AOSP_PERMISSIONS"].keys())

        for f, _ in self.get_fields():
            data = "%s-%s-%s" % (f.var[0], f.var[2], f.var[1])
            if data in list(
                    self.API_PERMISSION_MAPPINGS_MODULE[
                        "AOSP_PERMISSIONS_BY_FIELDS"].keys()):
                perm_intersection = pn.intersection(
                    self.API_PERMISSION_MAPPINGS_MODULE[
                        "AOSP_PERMISSIONS_BY_FIELDS"][data])
                for p in perm_intersection:
                    try:
                        permissions[p].extend(self.toPathVariable(f))
                    except KeyError:
                        permissions[p] = []
                        permissions[p].extend(self.toPathVariable(f))

        return permissions

    # global functions
    def get_strings(self):
        for i in self.__vars[TAINTED_STRING]:
            yield self.__vars[TAINTED_STRING][i], i

    def get_fields(self):
        for i in self.__vars[TAINTED_FIELD]:
            yield self.__vars[TAINTED_FIELD][i], i

    # specifics functions
    def get_strings_by_method(self, method):
        z = {}

        try:
            for i in self.__cache_string_by_method[method.get_method_idx()]:
                z[i] = []
                for j in i.get_paths():
                    if method.get_method_idx() == j[1]:
                        z[i].append(j[0])

            return z
        except:
            return z

    def get_fields_by_method(self, method):
        z = {}

        try:
            for i in self.__cache_field_by_method[method.get_method_idx()]:
                z[i] = []
                for j in i.get_paths():
                    if method.get_method_idx() == j[1]:
                        z[i].append(j[0])
            return z
        except:
            return z

    def add(self, var, _type, _method=None):
        if _type == TAINTED_FIELD:
            key = var[0] + var[1] + var[2]
            if key not in self.__vars[TAINTED_FIELD]:
                self.__vars[TAINTED_FIELD][key] = TaintedVariable(var, _type)
        elif _type == TAINTED_STRING:
            if var not in self.__vars[TAINTED_STRING]:
                self.__vars[TAINTED_STRING][var] = TaintedVariable(var, _type)
        elif _type == TAINTED_LOCAL_VARIABLE:
            if _method not in self.__vars[TAINTED_LOCAL_VARIABLE]:
                self.__vars[TAINTED_LOCAL_VARIABLE][_method] = {}

            if var not in self.__vars[TAINTED_LOCAL_VARIABLE][_method]:
                self.__vars[TAINTED_LOCAL_VARIABLE][_method][
                    var] = TaintedVariable(var, _type)

    def push_info(self, _type, var, access, idx, ref):
        if _type == TAINTED_FIELD:
            self.add(var, _type)
            key = var[0] + var[1] + var[2]
            self.__vars[_type][key].push(access, idx, ref)

            method_idx = ref.get_method_idx()
            if method_idx not in self.__cache_field_by_method:
                self.__cache_field_by_method[method_idx] = set()

            self.__cache_field_by_method[method_idx].add(
                self.__vars[TAINTED_FIELD][key])

        elif _type == TAINTED_STRING:
            self.add(var, _type)
            self.__vars[_type][var].push(access, idx, ref)

            method_idx = ref.get_method_idx()

            if method_idx not in self.__cache_string_by_method:
                self.__cache_string_by_method[method_idx] = set()

            self.__cache_string_by_method[method_idx].add(
                self.__vars[TAINTED_STRING][var])


class PathP(object):

    def __init__(self, access, idx, src_idx, dst_idx, vm):
        self.access_flag = access
        self.idx = idx
        self.src_idx = src_idx
        self.dst_idx = dst_idx
        self.vm = vm

    def get_access_flag(self):
        return self.access_flag

    def get_dst(self, cm):
        method = cm.get_method_ref(self.dst_idx)
        return method.get_class_name(), method.get_name(), method.get_descriptor()

    def get_src(self, cm):
        method = cm.get_method_ref(self.src_idx)
        return method.get_class_name(), method.get_name(), method.get_descriptor()

    def get_idx(self):
        return self.idx

    def get_src_idx(self):
        return self.src_idx

    def get_dst_idx(self):
        return self.dst_idx


class TaintedPackage(object):

    def __init__(self, vm, name):
        self.vm = vm
        self.name = name
        self.paths = {TAINTED_PACKAGE_CREATE: [], TAINTED_PACKAGE_CALL: []}

    def get_name(self):
        return self.name

    def gets(self):
        return self.paths

    def push(self, access, idx, src_idx, dst_idx):
        p = PathP(access, idx, src_idx, dst_idx, self.vm)
        self.paths[access].append(p)
        return p

    def get_objects_paths(self):
        return self.paths[TAINTED_PACKAGE_CREATE]

    def search_method(self, name, descriptor):
        """
            @param name : a regexp for the name of the method
            @param descriptor : a regexp for the descriptor of the method

            @rtype : a list of called paths
        """
        l = []
        m_name = re.compile(name)
        m_descriptor = re.compile(descriptor)

        for path in self.paths[TAINTED_PACKAGE_CALL]:
            _, dst_name, dst_descriptor = path.get_dst(
                self.vm.get_class_manager())
            if m_name.match(dst_name) is not None and m_descriptor.match(dst_descriptor) is not None:
                l.append(path)
        return l

    def get_method(self, name, descriptor):
        l = []
        for path in self.paths[TAINTED_PACKAGE_CALL]:
            if path.get_name() == name and path.get_descriptor() == descriptor:
                l.append(path)
        return l

    def get_paths(self):
        for i in self.paths:
            for j in self.paths[i]:
                yield j

    def get_paths_length(self):
        x = 0
        for i in self.paths:
            x += len(self.paths[i])
        return x

    def get_methods(self):
        return [path for path in self.paths[TAINTED_PACKAGE_CALL]]

    def get_new(self):
        return [path for path in self.paths[TAINTED_PACKAGE_CREATE]]

    def show(self):
        return
        cm = self.vm.get_class_manager()
        print(self.get_name())
        for _type in self.paths:
            print("\t -->", _type)
            if _type == TAINTED_PACKAGE_CALL:
                for path in self.paths[_type]:
                    print("\t\t => %s <-- %x in %s" %
                          (path.get_dst(cm), path.get_idx(), path.get_src(cm)))
            else:
                for path in self.paths[_type]:
                    print("\t\t => %x in %s" %
                          (path.get_idx(), path.get_src(cm)))


class TaintedPackages(object):

    def __init__(self, _vm):
        self.__vm = _vm
        self.__packages = {}
        self.__methods = {}

        self.AOSP_PERMISSIONS_MODULE = load_api_specific_resource_module(
            "aosp_permissions", self.__vm.get_api_version())
        self.API_PERMISSION_MAPPINGS_MODULE = load_api_specific_resource_module(
            "api_permission_mappings", self.__vm.get_api_version())

    def _add_pkg(self, name):
        if name not in self.__packages:
            self.__packages[name] = TaintedPackage(self.__vm, name)

    #self.context.get_tainted_packages().push_info( method_info[0], TAINTED_PACKAGE_CALL, idx, self, self.method, method_info[1], method_info[2][0] + method_info[2][1] )
    def push_info(self, class_name, access, idx, method, idx_method):
        self._add_pkg(class_name)
        p = self.__packages[class_name].push(
            access, idx, method.get_method_idx(), idx_method)

        try:
            self.__methods[method][class_name].append(p)
        except:
            try:
                self.__methods[method][class_name] = []
            except:
                self.__methods[method] = {}
                self.__methods[method][class_name] = []

            self.__methods[method][class_name].append(p)

    def get_packages_by_method(self, method):
        try:
            return self.__methods[method]
        except KeyError:
            return {}

    def get_package(self, name):
        return self.__packages[name]

    def get_packages_by_bb(self, bb):
        """
            :rtype: return a list of packaged used in a basic block
        """
        l = []
        for i in self.__packages:
            paths = self.__packages[i].gets()
            for j in paths:
                for k in paths[j]:
                    if k.get_bb() == bb:
                        l.append((i, k.get_access_flag(),
                                  k.get_idx(), k.get_method()))

        return l

    def get_packages(self):
        for i in self.__packages:
            yield self.__packages[i], i

    def get_internal_packages_from_package(self, package):
        classes = self.__vm.get_classes_names()
        l = []
        for m, _ in self.get_packages():
            paths = m.get_methods()
            for j in paths:
                src_class_name, _, _ = j.get_src(self.__vm.get_class_manager())
                dst_class_name, _, _ = j.get_dst(self.__vm.get_class_manager())

                if src_class_name == package and dst_class_name in classes:
                    l.append(j)
        return l

    def get_internal_packages(self):
        """
            :rtype: return a list of the internal packages called in the application
        """
        classes = self.__vm.get_classes_names()
        l = []
        for m, _ in self.get_packages():
            paths = m.get_methods()
            for j in paths:
                if j.get_access_flag() == TAINTED_PACKAGE_CALL:
                    dst_class_name, _, _ = j.get_dst(
                        self.__vm.get_class_manager())
                    if dst_class_name in classes and m.get_name() in classes:
                        l.append(j)
        return l

    def get_internal_new_packages(self):
        """
            :rtype: return a list of the internal packages created in the application
        """
        classes = self.__vm.get_classes_names()
        l = {}
        for m, _ in self.get_packages():
            paths = m.get_new()
            for j in paths:
                src_class_name, _, _ = j.get_src(self.__vm.get_class_manager())
                if src_class_name in classes and m.get_name() in classes:
                    if j.get_access_flag() == TAINTED_PACKAGE_CREATE:
                        try:
                            l[m.get_name()].append(j)
                        except:
                            l[m.get_name()] = []
                            l[m.get_name()].append(j)
        return l

    def get_external_packages(self):
        """
            :rtype: return a list of the external packages called in the application
        """
        classes = self.__vm.get_classes_names()
        l = []
        for m, _ in self.get_packages():
            paths = m.get_methods()
            for j in paths:
                src_class_name, _, _ = j.get_src(self.__vm.get_class_manager())
                dst_class_name, _, _ = j.get_dst(self.__vm.get_class_manager())
                if src_class_name in classes and dst_class_name not in classes:
                    if j.get_access_flag() == TAINTED_PACKAGE_CALL:
                        l.append(j)
        return l

    def search_packages(self, package_name):
        """
            :param package_name: a regexp for the name of the package

            :rtype: a list of called packages' paths
        """
        ex = re.compile(package_name)

        l = []
        for m, _ in self.get_packages():
            if ex.search(m.get_name()) is not None:
                l.extend(m.get_methods())
        return l

    def search_unique_packages(self, package_name):
        """
            :param package_name: a regexp for the name of the package
        """
        ex = re.compile(package_name)

        l = []
        d = {}
        for m, _ in self.get_packages():
            if ex.match(m.get_info()) is not None:
                for path in m.get_methods():
                    try:
                        d[path.get_class_name() + path.get_name() +
                          path.get_descriptor()] += 1
                    except KeyError:
                        d[path.get_class_name() + path.get_name() +
                          path.get_descriptor()] = 0
                        l.append([path.get_class_name(),
                                  path.get_name(), path.get_descriptor()])
        return l, d

    def search_methods(self, class_name, name, descriptor, re_expr=True):
        """
            @param class_name : a regexp for the class name of the method (the package)
            @param name : a regexp for the name of the method
            @param descriptor : a regexp for the descriptor of the method

            @rtype : a list of called methods' paths
        """
        l = []
        if re_expr:
            ex = re.compile(class_name)

            for m, _ in self.get_packages():
                if ex.search(m.get_name()) is not None:
                    l.extend(m.search_method(name, descriptor))

        return l

    def search_objects(self, class_name):
        """
            @param class_name : a regexp for the class name

            @rtype : a list of created objects' paths
        """
        ex = re.compile(class_name)
        l = []

        for m, _ in self.get_packages():
            if ex.search(m.get_name()) is not None:
                l.extend(m.get_objects_paths())

        return l

    def search_crypto_packages(self):
        """
            @rtype : a list of called crypto packages
        """
        return self.search_packages("Ljavax/crypto/")

    def search_telephony_packages(self):
        """
            @rtype : a list of called telephony packages
        """
        return self.search_packages("Landroid/telephony/")

    def search_net_packages(self):
        """
            @rtype : a list of called net packages
        """
        return self.search_packages("Landroid/net/")

    def get_method(self, class_name, name, descriptor):
        try:
            return self.__packages[class_name].get_method(name, descriptor)
        except KeyError:
            return []

    def get_permissions_method(self, method):
        permissions = set()
        for m, _ in self.get_packages():
            paths = m.get_methods()
            for j in paths:
                if j.get_method() == method:
                    if j.get_access_flag() == TAINTED_PACKAGE_CALL:
                        dst_class_name, dst_method_name, dst_descriptor = \
                            j.get_dst(self.__vm.get_class_manager())
                        data = "%s-%s-%s" % (
                            dst_class_name,
                            dst_method_name, dst_descriptor)
                        if data in list(
                                self.API_PERMISSION_MAPPINGS_MODULE[
                                    "AOSP_PERMISSIONS_BY_METHODS"].keys()):
                            permissions.update(
                                self.API_PERMISSION_MAPPINGS_MODULE[
                                    "AOSP_PERMISSIONS_BY_METHODS"][data])

        return permissions

    def get_permissions(self, permissions_needed):
        """
            @param permissions_needed : a list of restricted permissions to get
                                        ([] returns all permissions)
            @rtype : a dictionnary of permissions' paths
        """
        permissions = {}

        pn = set(permissions_needed)
        if permissions_needed == []:
            pn = set(self.AOSP_PERMISSIONS_MODULE["AOSP_PERMISSIONS"].keys())

        classes = self.__vm.get_classes_names()

        for m, _ in self.get_packages():
            paths = m.get_methods()
            for j in paths:
                src_class_name, src_method_name, src_descriptor = j.get_src(
                    self.__vm.get_class_manager())
                dst_class_name, dst_method_name, dst_descriptor = j.get_dst(
                    self.__vm.get_class_manager())
                if (src_class_name in classes) and (
                        dst_class_name not in classes):
                    if j.get_access_flag() == TAINTED_PACKAGE_CALL:
                        data = "%s-%s-%s" % (
                            dst_class_name,
                            dst_method_name, dst_descriptor)
                        if data in list(
                                self.API_PERMISSION_MAPPINGS_MODULE[
                                    "AOSP_PERMISSIONS_BY_METHODS"].keys()):
                            perm_intersection = pn.intersection(
                                self.API_PERMISSION_MAPPINGS_MODULE[
                                    "AOSP_PERMISSIONS_BY_METHODS"][data])
                            for p in perm_intersection:
                                try:
                                    permissions[p].append(j)
                                except KeyError:
                                    permissions[p] = []
                                    permissions[p].append(j)

        return permissions


class Enum(object):
    def __init__(self, names):
        self.names = names
        for value, name in enumerate(self.names):
            setattr(self, name.upper(), value)

    def tuples(self):
        return tuple(enumerate(self.names))


TAG_ANDROID = Enum(
    ['ANDROID', 'TELEPHONY', 'SMS', 'SMSMESSAGE', 'ACCESSIBILITYSERVICE',
     'ACCOUNTS', 'ANIMATION', 'APP', 'BLUETOOTH', 'CONTENT', 'DATABASE',
     'DEBUG', 'DRM', 'GESTURE', 'GRAPHICS', 'HARDWARE', 'INPUTMETHODSERVICE',
     'LOCATION', 'MEDIA', 'MTP', 'NET', 'NFC', 'OPENGL', 'OS', 'PREFERENCE',
     'PROVIDER', 'RENDERSCRIPT', 'SAX', 'SECURITY', 'SERVICE', 'SPEECH',
     'SUPPORT', 'TEST', 'TEXT', 'UTIL', 'VIEW', 'WEBKIT', 'WIDGET',
     'DALVIK_BYTECODE', 'DALVIK_SYSTEM', 'JAVA_REFLECTION'])

TAG_REVERSE_ANDROID = dict((i[0], i[1]) for i in TAG_ANDROID.tuples())

TAGS_ANDROID = {
    TAG_ANDROID.ANDROID: [0, "Landroid"],
    TAG_ANDROID.TELEPHONY: [0, "Landroid/telephony"],
    TAG_ANDROID.SMS: [0, "Landroid/telephony/SmsManager"],
    TAG_ANDROID.SMSMESSAGE: [0, "Landroid/telephony/SmsMessage"],
    TAG_ANDROID.DEBUG: [0, "Landroid/os/Debug"],
    TAG_ANDROID.ACCESSIBILITYSERVICE: [0, "Landroid/accessibilityservice"],
    TAG_ANDROID.ACCOUNTS: [0, "Landroid/accounts"],
    TAG_ANDROID.ANIMATION: [0, "Landroid/animation"],
    TAG_ANDROID.APP: [0, "Landroid/app"],
    TAG_ANDROID.BLUETOOTH: [0, "Landroid/bluetooth"],
    TAG_ANDROID.CONTENT: [0, "Landroid/content"],
    TAG_ANDROID.DATABASE: [0, "Landroid/database"],
    TAG_ANDROID.DRM: [0, "Landroid/drm"],
    TAG_ANDROID.GESTURE: [0, "Landroid/gesture"],
    TAG_ANDROID.GRAPHICS: [0, "Landroid/graphics"],
    TAG_ANDROID.HARDWARE: [0, "Landroid/hardware"],
    TAG_ANDROID.INPUTMETHODSERVICE: [0, "Landroid/inputmethodservice"],
    TAG_ANDROID.LOCATION: [0, "Landroid/location"],
    TAG_ANDROID.MEDIA: [0, "Landroid/media"],
    TAG_ANDROID.MTP: [0, "Landroid/mtp"],
    TAG_ANDROID.NET: [0, "Landroid/net"],
    TAG_ANDROID.NFC: [0, "Landroid/nfc"],
    TAG_ANDROID.OPENGL: [0, "Landroid/opengl"],
    TAG_ANDROID.OS: [0, "Landroid/os"],
    TAG_ANDROID.PREFERENCE: [0, "Landroid/preference"],
    TAG_ANDROID.PROVIDER: [0, "Landroid/provider"],
    TAG_ANDROID.RENDERSCRIPT: [0, "Landroid/renderscript"],
    TAG_ANDROID.SAX: [0, "Landroid/sax"],
    TAG_ANDROID.SECURITY: [0, "Landroid/security"],
    TAG_ANDROID.SERVICE: [0, "Landroid/service"],
    TAG_ANDROID.SPEECH: [0, "Landroid/speech"],
    TAG_ANDROID.SUPPORT: [0, "Landroid/support"],
    TAG_ANDROID.TEST: [0, "Landroid/test"],
    TAG_ANDROID.TEXT: [0, "Landroid/text"],
    TAG_ANDROID.UTIL: [0, "Landroid/util"],
    TAG_ANDROID.VIEW: [0, "Landroid/view"],
    TAG_ANDROID.WEBKIT: [0, "Landroid/webkit"],
    TAG_ANDROID.WIDGET: [0, "Landroid/widget"],
    TAG_ANDROID.DALVIK_BYTECODE: [0, "Ldalvik/bytecode"],
    TAG_ANDROID.DALVIK_SYSTEM: [0, "Ldalvik/system"],
    TAG_ANDROID.JAVA_REFLECTION: [0, "Ljava/lang/reflect"],
}


class Tags(object):
    """
      Handle specific tags

      :param patterns:
      :params reverse:
  """

    def __init__(self, patterns=TAGS_ANDROID, reverse=TAG_REVERSE_ANDROID):
        self.tags = set()

        self.patterns = patterns
        self.reverse = TAG_REVERSE_ANDROID

        for i in self.patterns:
            self.patterns[i][1] = re.compile(self.patterns[i][1])

    def emit(self, method):
        for i in self.patterns:
            if self.patterns[i][0] == 0:
                if self.patterns[i][1].search(method.get_class()) is not None:
                    self.tags.add(i)

    def emit_by_classname(self, classname):
        for i in self.patterns:
            if self.patterns[i][0] == 0:
                if self.patterns[i][1].search(classname) is not None:
                    self.tags.add(i)

    def get_list(self):
        return [self.reverse[i] for i in self.tags]

    def __contains__(self, key):
        return key in self.tags

    def __str__(self):
        return str([self.reverse[i] for i in self.tags])

    def empty(self):
        return self.tags == set()


class BasicBlocks(object):
    """
        This class represents all basic blocks of a method
    """

    def __init__(self, _vm, tv):
        self.__vm = _vm
        self.tainted = tv
        self.bb = []

    def push(self, bb):
        self.bb.append(bb)

    def pop(self, idx):
        return self.bb.pop(idx)

    def get_basic_block(self, idx):
        for i in self.bb:
            if i.get_start() <= idx < i.get_end():
                return i
        return None

    def get_tainted_integers(self):
        try:
            return self.tainted.get_tainted_integers()
        except:
            return None

    def get_tainted_packages(self):
        try:
            return self.tainted.get_tainted_packages()
        except:
            return None

    def get_tainted_variables(self):
        try:
            return self.tainted.get_tainted_variables()
        except:
            return None

    def get(self):
        """
            :rtype: return each basic block (:class:`DVMBasicBlock` object)
        """
        for i in self.bb:
            yield i

    def gets(self):
        """
            :rtype: a list of basic blocks (:class:`DVMBasicBlock` objects)
        """
        return self.bb

    def get_basic_block_pos(self, idx):
        return self.bb[idx]


class ExceptionAnalysis:
    def __init__(self, exception, bb):
        self.start = exception[0]
        self.end = exception[1]

        self.exceptions = exception[2:]

        for i in self.exceptions:
            i.append(bb.get_basic_block(i[1]))

    def show_buff(self):
        buff = "%x:%x\n" % (self.start, self.end)

        for i in self.exceptions:
            if i[2] is None:
                buff += "\t(%s -> %x %s)\n" % (i[0], i[1], i[2])
            else:
                buff += "\t(%s -> %x %s)\n" % (i[0], i[1], i[2].get_name())

        return buff[:-1]

    def get(self):
        d = {"start": self.start, "end": self.end, "list": []}

        for i in self.exceptions:
            d["list"].append({"name": i[0], "idx": i[1], "bb": i[2].get_name()})

        return d


class Exceptions:
    def __init__(self, _vm):
        self.__vm = _vm
        self.exceptions = []

    def add(self, exceptions, basic_blocks):
        for i in exceptions:
            self.exceptions.append(ExceptionAnalysis(i, basic_blocks))

    def get_exception(self, addr_start, addr_end):
        for i in self.exceptions:
            if i.start >= addr_start and i.end <= addr_end:
                return i

            elif addr_end <= i.end and addr_start >= i.start:
                return i

        return None

    def gets(self):
        return self.exceptions

    def get(self):
        for i in self.exceptions:
            yield i


class MethodAnalysis:
    def __init__(self, vm, method):
        """
        This class analyses in details a method of a class/dex file
        It is a wrapper around a :class:`EncodedMethod` and enhances it
        by using multiple :class:`BasicBlock`.

        :type vm: a :class:`DalvikVMFormat` object
        :type method: a :class:`EncodedMethod` object
        """

    def __init__(self, vm, method, tv):
        self.__vm = vm
        self.method = method

        self.tainted = tv

        self.basic_blocks = BasicBlocks(self.__vm, self.tainted)
        self.exceptions = Exceptions(self.__vm)

        self.code = self.method.get_code()
        if self.code:
            self._create_basic_block()

    def _create_basic_block(self):
        current_basic = DVMBasicBlock(0, self.__vm, self.method, self.basic_blocks)
        self.basic_blocks.push(current_basic)

        bc = self.code.get_bc()
        l = []
        h = {}
        idx = 0

        log.debug("Parsing instructions")
        for i in bc.get_instructions():
            for j in BasicOPCODES:
                if j.match(i.get_name()) is not None:
                    v = dvm.determineNext(i, idx, self.method)
                    h[idx] = v
                    l.extend(v)
                    break

            idx += i.get_length()

        log.debug("Parsing exceptions")
        excepts = dvm.determineException(self.__vm, self.method)
        for i in excepts:
            l.extend([i[0]])
            for handler in i[2:]:
                l.append(handler[1])

        log.debug("Creating basic blocks in %s" % self.method)
        idx = 0
        for i in bc.get_instructions():
            # index is a destination
            if idx in l:
                if current_basic.get_nb_instructions() != 0:
                    current_basic = DVMBasicBlock(current_basic.get_end(), self.__vm, self.method, self.basic_blocks)
                    self.basic_blocks.push(current_basic)

            current_basic.push(i)

            # index is a branch instruction
            if idx in h:
                current_basic = DVMBasicBlock(current_basic.get_end(), self.__vm, self.method, self.basic_blocks)
                self.basic_blocks.push(current_basic)

            idx += i.get_length()

        if current_basic.get_nb_instructions() == 0:
            self.basic_blocks.pop(-1)

        log.debug("Settings basic blocks childs")

        for i in self.basic_blocks.get():
            try:
                i.set_childs(h[i.end - i.get_last_length()])
            except KeyError:
                i.set_childs([])

        log.debug("Creating exceptions")

        # Create exceptions
        self.exceptions.add(excepts, self.basic_blocks)

        for i in self.basic_blocks.get():
            # setup exception by basic block
            i.set_exception_analysis(self.exceptions.get_exception(i.start, i.end - 1))

    def get_basic_blocks(self):
        """
            :rtype: a :class:`BasicBlocks` object
        """
        return self.basic_blocks

    def get_length(self):
        """
            :rtype: an integer which is the length of the code
        """
        return self.code.get_length() if self.code else 0

    def get_vm(self):
        return self.__vm

    def get_method(self):
        return self.method

    def show(self):
        """
        Prints the content of this method to stdout.

        This will print the method signature and the decompiled code.
        """
        args, ret = self.method.get_descriptor()[1:].split(")")
        if self.code:
            # We patch the descriptor here and add the registers, if code is available
            args = args.split(" ")

            reg_len = self.code.get_registers_size()
            nb_args = len(args)

            start_reg = reg_len - nb_args
            args = ["{} v{}".format(a, start_reg + i) for i, a in enumerate(args)]

        print("METHOD {} {} {} ({}){}".format(
              self.method.get_class_name(),
              self.method.get_access_flags_string(),
              self.method.get_name(),
              ", ".join(args), ret))
        bytecode.PrettyShow(self, self.basic_blocks.gets(), self.method.notes)

    def __repr__(self):
        return "<analysis.MethodAnalysis {}>".format(self.method)


class StringAnalysis:
    def __init__(self, value):
        """
        StringAnalysis contains the XREFs of a string.

        As Strings are only used as a source, they only contain
        the XREF_FROM set, i.e. where the string is used.

        This Array stores the information in which method the String is used.
        """
        self.value = value
        self.orig_value = value
        self.xreffrom = set()

    def AddXrefFrom(self, classobj, methodobj):
        self.xreffrom.add((classobj, methodobj))

    def get_xref_from(self):
        return self.xreffrom

    def set_value(self, value):
        self.value = value

    def get_value(self):
        return self.value

    def get_orig_value(self):
        return self.orig_value

    def __str__(self):
        data = "XREFto for string %s in\n" % repr(self.get_value())
        for ref_class, ref_method in self.xreffrom:
            data += "%s:%s\n" % (ref_class.get_vm_class().get_name(), ref_method)
        return data

    def __repr__(self):
        # TODO should remove all chars that are not pleasent. e.g. newlines
        if len(self.get_value()) > 20:
            s = "'{}'...".format(self.get_value()[:20])
        else:
            s = "'{}'".format(self.get_value())
        return "<analysis.StringAnalysis {}>".format(s)


class MethodClassAnalysis:
    def __init__(self, method):
        """
        MethodClassAnalysis contains the XREFs for a given method.

        Both referneces to other methods (XREF_TO) as well as methods calling
        this method (XREF_FROM) are saved.

        :param method: `dvm.EncodedMethod`
        """
        self.method = method
        self.xrefto = set()
        self.xreffrom = set()

        # Reserved for further use
        self.apilist = None

    def AddXrefTo(self, classobj, methodobj, offset):
        """
        Add a crossreference to another method
        (this method calls another method)

        :param classobj: :class:`~ClassAnalysis`
        :param methodobj:  :class:`~androguard.core.bytecodes.dvm.EncodedMethod`
        :param offset: integer where in the method the call happens
        """
        self.xrefto.add((classobj, methodobj, offset))

    def AddXrefFrom(self, classobj, methodobj, offset):
        """
        Add a crossrefernece from another method
        (this method is called by another method)

        :param classobj: :class:`~ClassAnalysis`
        :param methodobj:  :class:`~androguard.core.bytecodes.dvm.EncodedMethod`
        :param offset: integer where in the method the call happens
        """
        self.xreffrom.add((classobj, methodobj, offset))

    def get_xref_from(self):
        """
        Returns a list of three tuples cotaining the class, method and offset of
        the call, from where this object was called.

        The list of tuples has the form:
        (:class:`~ClassAnalysis`,
        :class:`~androguard.core.bytecodes.dvm.EncodedMethod` or
        :class:`~ExternalMethod`, int)
        """
        return self.xreffrom

    def get_xref_to(self):
        """
        Returns a list of three tuples cotaining the class, method and offset of
        the call, which are called by this method.

        The list of tuples has the form:
        (:class:`~ClassAnalysis`,
        :class:`~androguard.core.bytecodes.dvm.EncodedMethod` or
        :class:`~ExternalMethod`, int)
        """
        return self.xrefto

    def is_external(self):
        """
        Return True if the underlying methd is external

        :rtype: boolean
        """
        return isinstance(self.method, ExternalMethod)

    def is_android_api(self):
        """
        Returns True if the method seems to be an Android API method.

        This method might be not very precise unless an list of known API methods
        is given.

        :return: boolean
        """
        if not self.is_external():
            # Method must be external to be an API
            return False

        # Packages found at https://developer.android.com/reference/packages.html
        api_candidates = ["Landroid/", "Lcom/android/internal/util", "Ldalvik/", "Ljava/", "Ljavax/", "Lorg/apache/",
                          "Lorg/json/", "Lorg/w3c/dom/", "Lorg/xml/sax", "Lorg/xmlpull/v1/", "Ljunit/"]

        if self.apilist:
            # FIXME: This will not work... need to introduce a name for lookup (like EncodedMethod.__str__ but without
            # the offsert! Such a name is also needed for the lookup in permissions
            return self.method.get_name() in self.apilist
        else:
            for candidate in api_candidates:
                if self.method.get_class_name().startswith(candidate):
                    return True

        return False

    def get_method(self):
        """
        Return the `EncodedMethod` object that relates to this object
        :return: `dvm.EncodedMethod`
        """
        return self.method

    def __str__(self):
        data = "XREFto for %s\n" % self.method
        for ref_class, ref_method, offset in self.xrefto:
            data += "in\n"
            data += "%s:%s @0x%x\n" % (ref_class.get_vm_class().get_name(), ref_method, offset)

        data += "XREFFrom for %s\n" % self.method
        for ref_class, ref_method, offset in self.xreffrom:
            data += "in\n"
            data += "%s:%s @0x%x\n" % (ref_class.get_vm_class().get_name(), ref_method, offset)

        return data

    def __repr__(self):
        return "<analysis.MethodClassAnalysis {}{}>".format(self.method,
               " EXTERNAL" if isinstance(self.method, ExternalMethod) else "")


class FieldClassAnalysis:
    def __init__(self, field):
        """
        FieldClassAnalysis contains the XREFs for a class field.

        Instead of using XREF_FROM/XREF_TO, this object has methods for READ and
        WRITE access to the field.

        That means, that it will show you, where the field is read or written.

        :param field: `dvm.EncodedField`
        """
        self.field = field
        self.xrefread = set()
        self.xrefwrite = set()

    def AddXrefRead(self, classobj, methodobj):
        self.xrefread.add((classobj, methodobj))

    def AddXrefWrite(self, classobj, methodobj):
        self.xrefwrite.add((classobj, methodobj))

    def get_xref_read(self):
        return self.xrefread

    def get_xref_write(self):
        return self.xrefwrite

    def get_field(self):
        return self.field

    def __str__(self):
        data = "XREFRead for %s\n" % self.field
        for ref_class, ref_method in self.xrefread:
            data += "in\n"
            data += "%s:%s\n" % (ref_class.get_vm_class().get_name(), ref_method)

        data += "XREFWrite for %s\n" % self.field
        for ref_class, ref_method in self.xrefwrite:
            data += "in\n"
            data += "%s:%s\n" % (ref_class.get_vm_class().get_name(), ref_method)

        return data

    def __repr__(self):
        return "<analysis.FieldClassAnalysis {}->{}>".format(self.field.class_name, self.field.name)


class ExternalClass:
    def __init__(self, name):
        """
        The ExternalClass is used for all classes that are not defined in the
        DEX file, thus are external classes.

        :param name: Name of the external class
        """
        self.name = name
        self.methods = {}

    def get_methods(self):
        """
        Return the stored methods for this external class
        :return:
        """
        return self.methods.values()

    def GetMethod(self, name, descriptor):
        warnings.warn("deprecated, use get_method instead. This function might be removed in a later release!", DeprecationWarning)
        return self.get_method(name, descriptor)

    def get_method(self, name, descriptor):
        """
        Get the method by name and descriptor,
        or create a new one if the requested method does not exists.

        :param name: method name
        :param descriptor: method descriptor, for example `'(I)V'`
        :return: :class:`ExternalMethod`
        """
        key = name + str(descriptor)
        if key not in self.methods:
            self.methods[key] = ExternalMethod(self.name, name, descriptor)

        return self.methods[key]

    def get_name(self):
        """
        Returns the name of the ExternalClass object
        """
        return self.name

    def __repr__(self):
        return "<analysis.ExternalClass {}>".format(self.name)


class ExternalMethod:
    def __init__(self, class_name, name, descriptor):
        self.class_name = class_name
        self.name = name
        self.descriptor = descriptor

    def get_name(self):
        return self.name

    def get_class_name(self):
        return self.class_name

    def get_descriptor(self):
        return ''.join(self.descriptor)

    def get_access_flags_string(self):
        # TODO can we assume that external methods are always public?
        # they can also be static...
        # or constructor...
        return ""

    def __str__(self):
        return "%s->%s%s" % (self.class_name, self.name, ''.join(self.descriptor))

    def __repr__(self):
        return "<analysis.ExternalMethod {}>".format(self.__str__())


class ClassAnalysis:
    def __init__(self, classobj):
        """
        ClassAnalysis contains the XREFs from a given Class.

        Also external classes will generate xrefs, obviously only XREF_FROM are
        shown for external classes.

        :param classobj: class:`~androguard.core.bytecode.dvm.ClassDefItem` or :class:`ExternalClass`
        """

        # Automatically decide if the class is external or not
        self.external = isinstance(classobj, ExternalClass)

        self.orig_class = classobj
        self._inherits_methods = {}
        self._methods = {}
        self._fields = {}

        self.xrefto = collections.defaultdict(set)
        self.xreffrom = collections.defaultdict(set)

        # Reserved for further use
        self.apilist = None

    def is_external(self):
        """
        Tests wheather this class is an external class

        :return: True if the Class is external, False otherwise
        """
        return self.external

    def is_android_api(self):
        """
        Tries to guess if the current class is an Android API class.

        This might be not very precise unless an apilist is given, with classes that
        are in fact known APIs.
        Such a list might be generated by using the android.jar files.

        :return: boolean
        """

        # Packages found at https://developer.android.com/reference/packages.html
        api_candidates = ["Landroid/", "Lcom/android/internal/util", "Ldalvik/", "Ljava/", "Ljavax/", "Lorg/apache/",
                          "Lorg/json/", "Lorg/w3c/dom/", "Lorg/xml/sax", "Lorg/xmlpull/v1/", "Ljunit/"]

        if not self.is_external():
            # API must be external
            return False

        if self.apilist:
            return self.orig_class.get_name() in self.apilist
        else:
            for candidate in api_candidates:
                if self.orig_class.get_name().startswith(candidate):
                    return True

        return False

    def get_methods(self):
        """
        Return all `MethodClassAnalysis` objects of this class
        """
        return list(self._methods.values())

    def get_fields(self):
        """
        Return all `FieldClassAnalysis` objects of this class
        """
        return self._fields.values()

    def get_nb_methods(self):
        """
        Get the number of methods in this class
        """
        return len(self._methods)

    def get_method_analysis(self, method):
        """
        Return the MethodClassAnalysis object for a given EncodedMethod

        :param method: :class:`EncodedMethod`
        :return: :class:`MethodClassAnalysis`
        """
        return self._methods.get(method)

    def get_field_analysis(self, field):
        return self._fields.get(field)

    def get_fake_method(self, name, descriptor):
        """
        Search for the given method name and descriptor
        and return a fake (ExternalMethod) if required.

        :param name: name of the method
        :param descriptor: descriptor of the method, for example `'(I I I)V'`
        :return: :class:`ExternalMethod`
        """
        if self.external:
            # An external class can only generate the methods on demand
            return self.orig_class.get_method(name, descriptor)

        # We are searching an unknown method in this class
        # It could be something that the class herits
        key = name + str(descriptor)
        if key not in self._inherits_methods:
            self._inherits_methods[key] = ExternalMethod(self.orig_class.get_name(), name, descriptor)
        return self._inherits_methods[key]

    def AddFXrefRead(self, method, classobj, field):
        """
        Add a Field Read to this class

        :param method:
        :param classobj:
        :param field:
        :return:
        """
        if field not in self._fields:
            self._fields[field] = FieldClassAnalysis(field)
        self._fields[field].AddXrefRead(classobj, method)

    def AddFXrefWrite(self, method, classobj, field):
        """
        Add a Field Write to this class

        :param method:
        :param classobj:
        :param field:
        :return:
        """
        if field not in self._fields:
            self._fields[field] = FieldClassAnalysis(field)
        self._fields[field].AddXrefWrite(classobj, method)

    def AddMXrefTo(self, method1, classobj, method2, offset):
        if method1 not in self._methods:
            self._methods[method1] = MethodClassAnalysis(method1)
        self._methods[method1].AddXrefTo(classobj, method2, offset)

    def AddMXrefFrom(self, method1, classobj, method2, offset):
        if method1 not in self._methods:
            self._methods[method1] = MethodClassAnalysis(method1)
        self._methods[method1].AddXrefFrom(classobj, method2, offset)

    def AddXrefTo(self, ref_kind, classobj, methodobj, offset):
        """
        Creates a crossreference to another class.
        XrefTo means, that the current class calls another class.
        The current class should also be contained in the another class' XrefFrom list.

        :param ref_kind:
        :param classobj: :class:`ClassAnalysis` object to link
        :param methodobj:
        :param offset: Offset in the Methods Bytecode, where the call happens
        :return:
        """
        self.xrefto[classobj].add((ref_kind, methodobj, offset))

    def AddXrefFrom(self, ref_kind, classobj, methodobj, offset):
        """
        Creates a crossreference from this class.
        XrefFrom means, that the current class is called by another class.

        :param ref_kind:
        :param classobj: :class:`ClassAnalysis` object to link
        :param methodobj:
        :param offset: Offset in the methods bytecode, where the call happens
        :return:
        """
        self.xreffrom[classobj].add((ref_kind, methodobj, offset))

    def get_xref_from(self):
        return self.xreffrom

    def get_xref_to(self):
        return self.xrefto

    def get_vm_class(self):
        return self.orig_class

    def __repr__(self):
        return "<analysis.ClassAnalysis {}{}>".format(self.orig_class.get_name(),
                " EXTERNAL" if isinstance(self.orig_class, ExternalClass) else "")

    def __str__(self):
        # Print only instanceiations from other classes here
        # TODO also method xref and field xref should be printed?
        data = "XREFto for %s\n" % self.orig_class
        for ref_class in self.xrefto:
            data += str(ref_class.get_vm_class().get_name()) + " "
            data += "in\n"
            for ref_kind, ref_method, ref_offset in self.xrefto[ref_class]:
                data += "%d %s 0x%x\n" % (ref_kind, ref_method, ref_offset)

            data += "\n"

        data += "XREFFrom for %s\n" % self.orig_class
        for ref_class in self.xreffrom:
            data += str(ref_class.get_vm_class().get_name()) + " "
            data += "in\n"
            for ref_kind, ref_method, ref_offset in self.xreffrom[ref_class]:
                data += "%d %s 0x%x\n" % (ref_kind, ref_method, ref_offset)

            data += "\n"

        return data


class Analysis:
    def __init__(self, vm=None):
        """
        Analysis Object

        The Analysis contains a lot of information about (multiple) DalvikVMFormat objects
        Features are for example XREFs between Classes, Methods, Fields and Strings.

        Multiple DalvikVMFormat Objects can be added using the function `add`

        XREFs are created for:
        * classes (`ClassAnalysis`)
        * methods (`MethodClassAnalysis`)
        * strings (`StringAnalyis`)
        * fields (`FieldClassAnalysis`)

        :param vm: inital DalvikVMFormat object (default None)
        """

        # Contains DalvikVMFormat objects
        self.vms = []
        # A dict of {classname: ClassAnalysis}, populated on add(vm)
        self.classes = {}
        # A dict of {string: StringAnalysis}, populated on create_xref()
        self.strings = {}
        # A dict of {EncodedMethod: MethodAnalysis}, populated on add(vm)
        self.methods = {}

        if vm:
            self.add(vm)

    def add(self, vm):
        """
        Add a DalvikVMFormat to this Analysis

        :param vm: :class:`dvm.DalvikVMFormat` to add to this Analysis
        """
        self.vms.append(vm)
        self.tainted_variables = TaintedVariables(vm)
        self.tainted_packages = TaintedPackages(vm)

        self.tainted = {"variables": self.tainted_variables,
                        "packages": self.tainted_packages,
                        }
        for current_class in vm.get_classes():
            self.classes[current_class.get_name()] = ClassAnalysis(current_class)

        for method in vm.get_methods():
            self.methods[method] = MethodAnalysis(vm, method, self)

        for field in vm.get_all_fields():
            self.tainted_variables.add([
                field.get_class_name(),
                field.get_descriptor(),
                field.get_name()], TAINTED_FIELD)

    def _get_all_classes(self):
        """
        Returns all Class objects of all VMs in this Analysis
        Used by create_xref().
        """
        for vm in self.vms:
            for current_class in vm.get_classes():
                yield current_class

    def create_xref(self):
        """
        Create Class, Method, String and Field crossreferences
        for all classes in the Analysis.

        If you are using multiple DEX files, this function must
        be called when all DEX files are added.
        If you call the function after every DEX file, the
        crossreferences might be wrong!
        """
        log.debug("Creating Crossreferences (XREF)")
        tic = time.time()

        # TODO on concurrent runs, we probably need to clean up first,
        # or check that we do not write garbage.

        # TODO multiprocessing
        for c in self._get_all_classes():
            self._create_xref(c)

        log.info("End of creating cross references (XREF)")
        log.info("run time: {:0d}min {:02d}s".format(*divmod(int(time.time() - tic), 60)))

    def _create_xref(self, current_class):
        """
        Create the xref for `current_class`

        There are four steps involved in getting the xrefs:
        * Xrefs for classes
        *       for method calls
        *       for string usage
        *       for field manipulation

        All these information are stored in the *Analysis Objects.

        Note that this might be quite slow, as all instructions are parsed.

        :param current_class: :class:`dvm.ClassDefItem`
        """
        cur_cls_name = current_class.get_name()

        log.debug("Creating XREF/DREF for %s" % cur_cls_name)
        for current_method in current_class.get_methods():
            log.debug("Creating XREF for %s" % current_method)

            code = current_method.get_code()
            if code is None:
                continue

            off = 0
            for instruction in code.get_bc().get_instructions():
                op_value = instruction.get_op_value()

                # 1) check for class calls: const-class (0x1c), new-instance (0x22)
                if op_value in [0x1c, 0x22]:
                    idx_type = instruction.get_ref_kind()
                    # type_info is the string like 'Ljava/lang/Object;'
                    type_info = instruction.cm.vm.get_cm_type(idx_type)

                    # Internal xref related to class manipulation
                    # FIXME should the xref really only set if the class is in self.classes? If an external class is added later, it will be added too!
                    # See https://github.com/androguard/androguard/blob/d720ebf2a9c8e2a28484f1c81fdddbc57e04c157/androguard/core/analysis/analysis.py#L806
                    # Before the check would go for internal classes only!
                    if type_info != cur_cls_name:
                        if type_info not in self.classes:
                            # Create new external class
                            self.classes[type_info] = ClassAnalysis(ExternalClass(type_info))

                        cur_cls = self.classes[cur_cls_name]
                        oth_cls = self.classes[type_info]

                        cur_cls.AddXrefTo(ref_type[op_value], oth_cls, current_method, off)
                        oth_cls.AddXrefFrom(ref_type[op_value], cur_cls, current_method, off)

                # 2) check for method calls: invoke-* (0x6e ... 0x72), invoke-xxx/range (0x74 ... 0x78)
                elif (0x6e <= op_value <= 0x72) or (0x74 <= op_value <= 0x78):
                    idx_meth = instruction.get_ref_kind()
                    method_info = instruction.cm.vm.get_cm_method(idx_meth)
                    if method_info:
                        class_info = method_info[0]

                        for vm in self.vms:
                            method_item = vm.get_method_descriptor(method_info[0], method_info[1], ''.join(method_info[2]))
                            if method_item:
                                break

                        if not method_item:
                            if method_info[0] not in self.classes:
                                # Seems to be an external class, create it first
                                # Beware: if not all DEX files are loaded at the time create_xref runs
                                # you will run into problems!
                                self.classes[method_info[0]] = ClassAnalysis(ExternalClass(method_info[0]))
                            method_item = self.classes[method_info[0]].get_fake_method(method_info[1], method_info[2])

                        self.classes[cur_cls_name].AddMXrefTo(current_method, self.classes[class_info], method_item, off)
                        self.classes[class_info].AddMXrefFrom(method_item, self.classes[cur_cls_name], current_method, off)

                        # Internal xref related to class manipulation
                        if class_info in self.classes and class_info != cur_cls_name:
                            self.classes[cur_cls_name].AddXrefTo(REF_CLASS_USAGE, self.classes[class_info], method_item, off)
                            self.classes[class_info].AddXrefFrom(REF_CLASS_USAGE, self.classes[cur_cls_name], current_method, off)

                # 3) check for string usage: const-string (0x1a), const-string/jumbo (0x1b)
                elif 0x1a <= op_value <= 0x1b:
                    string_value = instruction.cm.vm.get_cm_string(instruction.get_ref_kind())
                    if string_value not in self.strings:
                        self.strings[string_value] = StringAnalysis(string_value)

                    # TODO: The bytecode offset is stored everywhere but not here?
                    # TODO there is no XrefTo in the method for a string
                    self.strings[string_value].AddXrefFrom(self.classes[cur_cls_name], current_method)

                # TODO maybe we should add a step 3a here and check for all const fields. You can then xref for integers etc!

                # 4) check for field usage: i*op (0x52 ... 0x5f), s*op (0x60 ... 0x6d)
                elif 0x52 <= op_value <= 0x6d:
                    idx_field = instruction.get_ref_kind()
                    field_info = instruction.cm.vm.get_cm_field(idx_field)
                    field_item = instruction.cm.vm.get_field_descriptor(field_info[0], field_info[2], field_info[1])
                    # TODO: The bytecode offset is stored everywhere but not here?
                    if field_item:
                        if (0x52 <= op_value <= 0x58) or (0x60 <= op_value <= 0x66):
                            # read access to a field
                            self.classes[cur_cls_name].AddFXrefRead(current_method, self.classes[cur_cls_name], field_item)
                        else:
                            # write access to a field
                            self.classes[cur_cls_name].AddFXrefWrite(current_method, self.classes[cur_cls_name], field_item)

                off += instruction.get_length()

    def get_method(self, method):
        """
        Get the :class:`MethodAnalysis` object for a given :class:`EncodedMethod`.
        This Analysis object is used to enhance EncodedMethods.

        :param method: :class:`EncodedMethod` to search for
        :return: :class:`MethodAnalysis` object for the given method, or None if method was not found
        """
        if method in self.methods:
            return self.methods[method]
        else:
            return None

    def get_method_by_name(self, class_name, method_name, method_descriptor):
        """
        Search for a :class:`EncodedMethod` in all classes in this analysis

        :param class_name: name of the class, for example 'Ljava/lang/Object;'
        :param method_name: name of the method, for example 'onCreate'
        :param method_descriptor: descriptor, for example '(I I Ljava/lang/String)V
        :return: :class:`EncodedMethod` or None if method was not found
        """
        if class_name in self.classes:
            for method in self.classes[class_name].get_vm_class().get_methods():
                if method.get_name() == method_name and method.get_descriptor() == method_descriptor:
                    return method
        return None

    def get_method_analysis(self, method):
        """
        Returns the crossreferencing object for a given Method.

        Beware: the similar named function :meth:`~get_method()` will return
        a :class:`MethodAnalysis` object, while this function returns a :class:`MethodClassAnalysis` object!

        This Method will only work after a run of :meth:`~create_xref()`

        :param method: :class:`EncodedMethod`
        :return: :class:`MethodClassAnalysis` for the given method or None, if method was not found
        """
        class_analysis = self.get_class_analysis(method.get_class_name())
        if class_analysis:
            return class_analysis.get_method_analysis(method)
        return None

    def get_method_analysis_by_name(self, class_name, method_name, method_descriptor):
        """
        Returns the crossreferencing object for a given method.

        This function is similar to :meth:`~get_method_analysis`, with the difference
        that you can look up the Method by name

        :param class_name: name of the class, for example `'Ljava/lang/Object;'`
        :param method_name: name of the method, for example `'onCreate'`
        :param method_descriptor: method descriptor, for example `'(I I)V'`
        :return: :class:`MethodClassAnalysis`
        """
        method = self.get_method_by_name(class_name, method_name, method_descriptor)
        if method:
            return self.get_method_analysis(method)
        return None

    def get_field_analysis(self, field):
        """
        Get the FieldAnalysis for a given fieldname

        :param field: TODO
        :return: :class:`FieldClassAnalysis`
        """
        class_analysis = self.get_class_analysis(field.get_class_name())
        if class_analysis:
            return class_analysis.get_field_analysis(field)
        return None

    def is_class_present(self, class_name):
        """
        Checks if a given class name is part of this Analysis.

        :param class_name: classname like 'Ljava/lang/Object;' (including L and ;)
        :return: True if class was found, False otherwise
        """
        return class_name in self.classes

    def get_class_analysis(self, class_name):
        """
        Returns the :class:`ClassAnalysis` object for a given classname.

        :param class_name: classname like 'Ljava/lang/Object;' (including L and ;)
        :return: :class:`ClassAnalysis`
        """
        return self.classes.get(class_name)

    def get_external_classes(self):
        """
        Returns all external classes, that means all classes that are not
        defined in the given set of `DalvikVMObjects`.

        :rtype: generator of `ClassAnalysis`
        """
        for cls in self.classes.values():
            if cls.is_external():
                yield cls

    def get_internal_classes(self):
        """
        Returns all external classes, that means all classes that are
        defined in the given set of :class:`~DalvikVMFormat`.

        :rtype: generator of :class:`~ClassAnalysis`
        """
        for cls in self.classes.values():
            if not cls.is_external():
                yield cls

    def get_strings_analysis(self):
        """
        Returns a dictionary of strings and their corresponding :class:`StringAnalysis`

        :return: a dictionary
        """
        return self.strings

    def get_strings(self):
        """
        Returns a list of :class:`StringAnalysis` objects

        :rtype: list of :class:`StringAnalysis`
        """
        return self.strings.values()

    def get_classes(self):
        """
        Returns a list of `ClassAnalysis` objects

        Returns both internal and external classes (if any)

        :rtype: list of :class:`ClassAnalysis`
        """
        return self.classes.values()

    def get_methods(self):
        """
        Returns a list of `MethodClassAnalysis` objects

        """
        for c in self.classes.values():
            for m in c.get_methods():
                yield m

    def get_fields(self):
        """
        Returns a list of `FieldClassAnalysis` objects

        """
        for c in self.classes.values():
            for f in c.get_fields():
                yield f

    def find_classes(self, name=".*", no_external=False):
        """
        Find classes by name, using regular expression
        This method will return all ClassAnalysis Object that match the name of
        the class.

        :param name: regular expression for class name (default ".*")
        :param no_external: Remove external classes from the output (default False)
        :rtype: generator of `ClassAnalysis`
        """
        for cname, c in self.classes.items():
            if no_external and isinstance(c.get_vm_class(), ExternalClass):
                continue
            if re.match(name, cname):
                yield c

    def find_methods(self, classname=".*", methodname=".*", descriptor=".*",
            accessflags=".*", no_external=False):
        """
        Find a method by name using regular expression.
        This method will return all MethodClassAnalysis objects, which match the
        classname, methodname, descriptor and accessflags of the method.

        :param classname: regular expression for the classname
        :param methodname: regular expression for the method name
        :param descriptor: regular expression for the descriptor
        :param accessflags: regular expression for the accessflags
        :param no_external: Remove external method from the output (default False)
        :rtype: generator of `MethodClassAnalysis`
        """
        for cname, c in self.classes.items():
            if re.match(classname, cname):
                for m in c.get_methods():
                    z = m.get_method()
                    # TODO is it even possible that an internal class has
                    # external methods? Maybe we should check for ExternalClass
                    # instead...
                    if no_external and isinstance(z, ExternalMethod):
                        continue
                    if re.match(methodname, z.get_name()) and \
                       re.match(descriptor, z.get_descriptor()) and \
                       re.match(accessflags, z.get_access_flags_string()):
                        yield m

    def find_strings(self, string=".*"):
        """
        Find strings by regex

        :param string: regular expression for the string to search for
        :rtype: generator of `StringAnalysis`
        """
        for s, sa in self.strings.items():
            if re.match(string, s):
                yield sa

    def find_fields(self, classname=".*", fieldname=".*", fieldtype=".*",
            accessflags=".*"):
        """
        find fields by regex

        :param classname: regular expression of the classname
        :param fieldname: regular expression of the fieldname
        :param fieldtype: regular expression of the fieldtype
        :param accessflags: regular expression of the access flags
        :rtype: generator of `FieldClassAnalysis`
        """
        for cname, c in self.classes.items():
            if re.match(classname, cname):
                for f in c.get_fields():
                    z = f.get_field()
                    if re.match(fieldname, z.get_name()) and \
                       re.match(fieldtype, z.get_descriptor()) and \
                       re.match(accessflags, z.get_access_flags_string()):
                           yield f

    def __repr__(self):
        return "<analysis.Analysis VMs: {}, Classes: {}, Strings: {}>".format(len(self.vms), len(self.classes), len(self.strings))

    def get_call_graph(self, classname=".*", methodname=".*", descriptor=".*",
                       accessflags=".*", no_isolated=False, entry_points=[]):
        """
        Generate a directed graph based on the methods found by the filters applied.
        The filters are the same as in
        :meth:`~androguard.core.analaysis.analaysis.Analysis.find_methods`

        A networkx.DiGraph is returned, containing all edges only once!
        that means, if a method calls some method twice or more often, there will
        only be a single connection.

        :param classname: regular expression of the classname (default: ".*")
        :param fieldname: regular expression of the fieldname (default: ".*")
        :param fieldtype: regular expression of the fieldtype (default: ".*")
        :param accessflags: regular expression of the access flags (default: ".*")
        :param no_isolated: remove isolated nodes from the graph, e.g. methods which do not call anything (default: False)
        :param entry_points: A list of classes that are marked as entry point

        :rtype: DiGraph
        """

        def _add_node(G, method, _entry_points):
            """
            Wrapper to add methods to a graph
            """
            if method not in G.node:
                if isinstance(method, ExternalMethod):
                    is_external = True
                else:
                    is_external = False

                if method.get_class_name() in _entry_points:
                    is_entry_point = True
                else:
                    is_entry_point = False

                G.add_node(method, external=is_external, entrypoint=is_entry_point)

        CG = nx.DiGraph()

        # Note: If you create the CG from many classes at the same time, the drawing
        # will be a total mess...
        for m in self.find_methods(classname=classname, methodname=methodname,
                                   descriptor=descriptor, accessflags=accessflags):
            orig_method = m.get_method()
            log.info("Found Method --> {}".format(orig_method))

            if no_isolated and len(m.get_xref_to()) == 0:
                log.info("Skipped {}, because if has no xrefs".format(orig_method))
                continue

            _add_node(CG, orig_method, entry_points)

            for other_class, callee, offset in m.get_xref_to():
                _add_node(CG, callee, entry_points)

                # As this is a DiGraph and we are not interested in duplicate edges,
                # check if the edge is already in the edge set.
                # If you need all calls, you probably want to check out MultiDiGraph
                if not CG.has_edge(orig_method, callee):
                    CG.add_edge(orig_method, callee)

        return CG

    def get_tainted_variables(self):
        """
           Return the tainted variables

           :rtype: a :class:`TaintedVariables` object
        """
        return self.tainted_variables

    def get_tainted_packages(self):
        """
           Return the tainted packages

           :rtype: a :class:`TaintedPackages` object
        """
        return self.tainted_packages

    def get_tainted_fields(self):
        return self.get_tainted_variables().get_fields()

    def get_tainted_field(self, class_name, name, descriptor):
        """
           Return a specific tainted field

           :param class_name: the name of the class
           :param name: the name of the field
           :param descriptor: the descriptor of the field
           :type class_name: string
           :type name: string
           :type descriptor: string

           :rtype: a :class:`TaintedVariable` object
        """
        return self.get_tainted_variables().get_field(
            class_name, name, descriptor)

    def get_permissions(self, permissions_needed):
        """
            Return the permissions used

            :param permissions_needed: a list of restricted permissions to get
                                        ([] returns all permissions)
            :type permissions_needed: list

            :rtype: a dictionnary of permissions paths
        """
        permissions = {}

        permissions.update(self.get_tainted_packages(
        ).get_permissions(permissions_needed))
        permissions.update(self.get_tainted_variables(
        ).get_permissions(permissions_needed))

        return permissions

    def get_permissions_method(self, method):
        permissions_f = self.get_tainted_packages().\
            get_permissions_method(method)
        permissions_v = self.get_tainted_variables().\
            get_permissions_method(method)

        all_permissions_of_method = permissions_f.union(permissions_v)

        return list(all_permissions_of_method)


def is_ascii_obfuscation(vm):
    """
    Tests if any class inside a DalvikVMObject
    uses ASCII Obfuscation (e.g. UTF-8 Chars in Classnames)

    :param vm: `DalvikVMObject`
    :return: True if ascii obfuscation otherwise False
    """
    for classe in vm.get_classes():
        if is_ascii_problem(classe.get_name()):
            return True
        for method in classe.get_methods():
            if is_ascii_problem(method.get_name()):
                return True
    return False
