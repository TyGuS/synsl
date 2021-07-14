

class BenchmarksDB {
    data: BenchmarksDB.Data

    constructor(data: BenchmarksDB.Data) {
        this.data = data;
    }

    getSpec(dir: string, fn: string): BenchmarksDB.Data.Spec {
        return {
            name: `${dir}:${fn}`, 
            defs: this.getDefs(dir),
            ...this.getInputSpec(dir, fn)
        };
    }

    getDefs(dir: string) {
        return Object.entries(this.data[dir])
            .map(([fn, txt]) => fn.endsWith('.def') && txt).filter(x => x);
    }

    getInputSpec(dir: string, fn: string) {
        var prog = this.data[dir][fn];
        return BenchmarksDB.Data.parseInputSpec(prog);
    }

    static async load(url = './benchmarks.db.json') {
        return new BenchmarksDB(await (await fetch(url)).json());
    }
}

namespace BenchmarksDB {
    export type Data = {[dir: string]: {[fn: string]: string}};

    export namespace Data {
        export type Spec = {
            name?: string
            defs: string[]
            in: string
            params?: string[]
        }

        export function parseSpec(name: string, text: string): Spec {
            return {name, defs: [], ...parseInputSpec(text)};
        }

        export function parseInputSpec(text: string) {
            var hashline = text.match(/^#[.]?(.*)\n([^]*)/),
                enclosure = text.match(/###+([^]*?)###+/),
                params = hashline?.[1].trim().split(/\s+/),
                in_ = enclosure?.[1] || hashline?.[2] || text;
            return {in: in_, params};
        }

        export function unparseSpec(spec: Spec) {
            var params = spec.params ? [`# ${spec.params.join(' ')}`] : [];
            return [...params, ...spec.defs, spec.in].join('\n');
        }
    }
}


export { BenchmarksDB }