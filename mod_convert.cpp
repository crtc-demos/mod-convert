// Based on PT2PLAY v0.57 which is:
// C port of Protracker 2's (v2.3a) replayer, by 8bitbubsy (Olav Sorensen)
// using the original asm source codes by Crayon (Peter Hanning) and ZAP (Lars Hamre)

#include "alfe/main.h"
#include "alfe/audio.h"
#include "alfe/space.h"
#include "alfe/hash_table.h"
#include "alfe/set.h"
#include "../libsamplerate-0.1.8/src/samplerate.h"

static const int commandArpeggio            = 0x000;
static const int commandPortaUp             = 0x100;
static const int commandPortaDown           = 0x200;
static const int commandTonePortamento      = 0x300;
static const int commandVibrato             = 0x400;
static const int commandTonePlusVolSlide    = 0x500;
static const int commandVibratoPlusVolSlide = 0x600;
static const int commandTremolo             = 0x700;
static const int commandSampleOffset        = 0x900;
static const int commandVolumeSlide         = 0xa00;
static const int commandPositionJump        = 0xb00;
static const int commandVolumeChange        = 0xc00;
static const int commandPatternBreak        = 0xd00;
static const int commandECommands           = 0xe00;
static const int commandFilter              = 0xe00;
static const int commandFinePortaUp         = 0xe10;
static const int commandFinePortaDown       = 0xe20;
static const int commandSetGlissControl     = 0xe30;
static const int commandSetVibratoControl   = 0xe40;
static const int commandSetFineTune         = 0xe50;
static const int commandJumpLoop            = 0xe60;
static const int commandSetTremoloControl   = 0xe70;
static const int commandRetrigNote          = 0xe90;
static const int commandVolumeFineUp        = 0xea0;
static const int commandVolumeFineDown      = 0xeb0;
static const int commandNoteCut             = 0xec0;
static const int commandNoteDelay           = 0xed0;
static const int commandPatternDelay        = 0xee0;
static const int commandFunkIt              = 0xef0;
static const int commandSetSpeed            = 0xf00;

static const UInt8 mt_VibratoTable[32] =
{
    0x00, 0x18, 0x31, 0x4A, 0x61, 0x78, 0x8D, 0xA1,
    0xB4, 0xC5, 0xD4, 0xE0, 0xEB, 0xF4, 0xFA, 0xFD,
    0xFF, 0xFD, 0xFA, 0xF4, 0xEB, 0xE0, 0xD4, 0xC5,
    0xB4, 0xA1, 0x8D, 0x78, 0x61, 0x4A, 0x31, 0x18
};

class NoteDescriptor
{
public:
    NoteDescriptor() { }
    NoteDescriptor(int sample, int period, int amplitude)
        : _sample(sample), _period(period), _amplitude(amplitude)
    {
        if (_amplitude == 0) {
            _period = 0;
            _sample = 0;
        }
    }
    int hash() const { return (_period*64 + _amplitude)*32 + _sample; }
    bool operator==(const NoteDescriptor& other) const
    {
        return _sample == other._sample && _period == other._period &&
            _amplitude == other._amplitude;
    }
    int period() const { return _period; }
    void clearPeriod() { _period = 0; }
    void quantizeVolume(int levels)
    {
        _amplitude = (_amplitude * levels + 32) / 64;
    }
    int sample() const { return _sample; }
    int amplitude() const { return _amplitude; }
private:
    int _sample;
    int _period;
    int _amplitude;
};

//const Byte* base;
//int ptr(const Byte* p) { return (p == 0 ? 0 : p - base); }
//
class ModPlayer : public Source<Int16>
{
public:
    ModPlayer(const Byte* mt_Data, int wavSampleRate, int mode, int volumeLevels, String inputFileName, bool noClamp)
      : _wavSampleRate(wavSampleRate), _mode(mode), _volumeLevels(volumeLevels), _inputFileName(inputFileName), _noClamp(noClamp)
    {
        //base = mt_Data;

        f_outputFreq = static_cast<float>(wavSampleRate);

        if (_mode == 0) {
            _amigaClock = 39375000.0/11;  // NTSC clock
            mt_TempoMode = 1;  // VBlank
            samplesPerFrame = 262;
            mt_TempoMode = 1;
        }
        else {
            _amigaClock = 3546895;  // PAL clock
            mt_TempoMode = 0;  // CIA
            samplesPerFrame = wavSampleRate / 50;
        }

        masterBuffer.allocate(samplesPerFrame);

        for (int i = 0; i < 4; ++i)
            mt_Chan[i].init(this);

        mt_SongDataPtr = mt_Data;

        UInt8 pattNum = 0;
        for (int i = 0; i < 128; ++i)
            pattNum = max(pattNum, mt_SongDataPtr[952 + i]);
        ++pattNum;

        const Int8* sampleStarts = reinterpret_cast<const Int8*>(
            &mt_SongDataPtr[1084 + (pattNum << 10)]);
        for (int i = 0; i < 31; ++i) {
            Sample s(sampleStarts, &mt_SongDataPtr[42 + 30*i]);
            _samples[i] = s;
            sampleStarts += _samples[i]._length << 1;
            //printf("%04x %02i %02i %02i %02i %02i\n", s._start - reinterpret_cast<const Int8*>(mt_Data), s._length, s._fineTune, s._volume, s._repeat, s._repeatLength);
        }

        mt_PattPosOff   = 0;
        mt_Speed        = 6;
        mt_Counter      = 6;
        mt_SongPos      = 0;
        mt_PatternPos   = 0;
        mt_PattDelTime  = 0;
        mt_PattDelTime2 = 0;
        mt_PBreakPos    = 0;
        mt_PosJumpFlag  = 0;
        mt_PBreakFlag   = 0;
        mt_LowMask      = 0xFF;
        mt_PattOff      = 1084 + ((UInt32)(mt_SongDataPtr[952]) << 10);
        _complete = false;
    }

    void checkComplete()
    {
        int phase = mt_SongPos;
        phase = (phase << 6) | (mt_PatternPos >> 4);
        for (int i = 0; i < 4; ++i)
            phase = (phase << 4) | (mt_Chan[i].loopCount());
        if (_phases.has(phase))
            _complete = true;
        else
            _phases.add(phase);
    }

    // Returns true if waves fit, false otherwise
    bool calculate()
    {
        console.write(String("Volume levels = ") + decimal(_volumeLevels) + "\n");
        console.write(String("Processing MOD\n"));
        do {
//    printf("%i %i %i %i ", mt_TempoMode, mt_SongPos, mt_PosJumpFlag, mt_PBreakFlag);
//    printf("%i %i %i %i ", 0, mt_PBreakPos, mt_PattDelTime, mt_PattDelTime2);
//    printf("%i %i %i %i ", ptr(mt_SongDataPtr), mt_LowMask, mt_Counter, mt_Speed);
//    printf("%i %i %i %i ", mt_PatternPos, mt_TimerVal, mt_PattPosOff, mt_PattOff);
//    printf("%f %i %i\n", f_outputFreq, 0, samplesPerFrame);
//
//#define private public
//
//    PT_CHN* AUD = mt_Chan;
//
//    PT_CHN& mt_Chan1temp = mt_Chan[0];
//    printf("%i %i %i %i ", mt_Chan1temp.n_note, mt_Chan1temp.n_cmd, ptr((const Byte*)mt_Chan1temp.n_start), ptr((const Byte*)mt_Chan1temp.n_wavestart));
//    printf("%i %i %i %i ", ptr((const Byte*)mt_Chan1temp.n_loopstart), mt_Chan1temp.n_volume, mt_Chan1temp.n_toneportdirec, mt_Chan1temp.n_vibratopos);
//    printf("%i %i %i %i ", mt_Chan1temp.n_tremolopos, mt_Chan1temp.n_pattpos, mt_Chan1temp.n_loopcount, mt_Chan1temp.n_wavecontrol);
//    printf("%i %i %i %i ", mt_Chan1temp.n_glissfunk, mt_Chan1temp.n_sampleoffset, mt_Chan1temp.n_toneportspeed, mt_Chan1temp.n_vibratocmd);
//    printf("%i %i %i %i ", mt_Chan1temp.n_tremolocmd, mt_Chan1temp.n_finetune, mt_Chan1temp.n_funkoffset, mt_Chan1temp.n_period);
//    printf("%i %i %i %i ", mt_Chan1temp.n_wantedperiod, mt_Chan1temp.n_length, mt_Chan1temp.n_replen, mt_Chan1temp.n_repend);
//    printf("%i %i %i %i ", ptr((const Byte*)AUD[0].DAT), ptr((const Byte*)AUD[0].REPDAT), AUD[0].TRIGGER, AUD[0].REPLEN);
//    printf("%i %i %f %f %f\n", AUD[0].POS, AUD[0].LEN, AUD[0].DELTA, AUD[0].FRAC, AUD[0].VOL);
//
//    PT_CHN& mt_Chan2temp = mt_Chan[1];
//    printf("%i %i %i %i ", mt_Chan2temp.n_note, mt_Chan2temp.n_cmd, ptr((const Byte*)mt_Chan2temp.n_start), ptr((const Byte*)mt_Chan2temp.n_wavestart));
//    printf("%i %i %i %i ", ptr((const Byte*)mt_Chan2temp.n_loopstart), mt_Chan2temp.n_volume, mt_Chan2temp.n_toneportdirec, mt_Chan2temp.n_vibratopos);
//    printf("%i %i %i %i ", mt_Chan2temp.n_tremolopos, mt_Chan2temp.n_pattpos, mt_Chan2temp.n_loopcount, mt_Chan2temp.n_wavecontrol);
//    printf("%i %i %i %i ", mt_Chan2temp.n_glissfunk, mt_Chan2temp.n_sampleoffset, mt_Chan2temp.n_toneportspeed, mt_Chan2temp.n_vibratocmd);
//    printf("%i %i %i %i ", mt_Chan2temp.n_tremolocmd, mt_Chan2temp.n_finetune, mt_Chan2temp.n_funkoffset, mt_Chan2temp.n_period);
//    printf("%i %i %i %i ", mt_Chan2temp.n_wantedperiod, mt_Chan2temp.n_length, mt_Chan2temp.n_replen, mt_Chan2temp.n_repend);
//    printf("%i %i %i %i ", ptr((const Byte*)AUD[1].DAT), ptr((const Byte*)AUD[1].REPDAT), AUD[1].TRIGGER, AUD[1].REPLEN);
//    printf("%i %i %f %f %f\n", AUD[1].POS, AUD[1].LEN, AUD[1].DELTA, AUD[1].FRAC, AUD[1].VOL);
//
//    PT_CHN& mt_Chan3temp = mt_Chan[2];
//    printf("%i %i %i %i ", mt_Chan3temp.n_note, mt_Chan3temp.n_cmd, ptr((const Byte*)mt_Chan3temp.n_start), ptr((const Byte*)mt_Chan3temp.n_wavestart));
//    printf("%i %i %i %i ", ptr((const Byte*)mt_Chan3temp.n_loopstart), mt_Chan3temp.n_volume, mt_Chan3temp.n_toneportdirec, mt_Chan3temp.n_vibratopos);
//    printf("%i %i %i %i ", mt_Chan3temp.n_tremolopos, mt_Chan3temp.n_pattpos, mt_Chan3temp.n_loopcount, mt_Chan3temp.n_wavecontrol);
//    printf("%i %i %i %i ", mt_Chan3temp.n_glissfunk, mt_Chan3temp.n_sampleoffset, mt_Chan3temp.n_toneportspeed, mt_Chan3temp.n_vibratocmd);
//    printf("%i %i %i %i ", mt_Chan3temp.n_tremolocmd, mt_Chan3temp.n_finetune, mt_Chan3temp.n_funkoffset, mt_Chan3temp.n_period);
//    printf("%i %i %i %i ", mt_Chan3temp.n_wantedperiod, mt_Chan3temp.n_length, mt_Chan3temp.n_replen, mt_Chan3temp.n_repend);
//    printf("%i %i %i %i ", ptr((const Byte*)AUD[2].DAT), ptr((const Byte*)AUD[2].REPDAT), AUD[2].TRIGGER, AUD[2].REPLEN);
//    printf("%i %i %f %f %f\n", AUD[2].POS, AUD[2].LEN, AUD[2].DELTA, AUD[2].FRAC, AUD[2].VOL);
//
//    PT_CHN& mt_Chan4temp = mt_Chan[3];
//    printf("%i %i %i %i ", mt_Chan4temp.n_note, mt_Chan4temp.n_cmd, ptr((const Byte*)mt_Chan4temp.n_start), ptr((const Byte*)mt_Chan4temp.n_wavestart));
//    printf("%i %i %i %i ", ptr((const Byte*)mt_Chan4temp.n_loopstart), mt_Chan4temp.n_volume, mt_Chan4temp.n_toneportdirec, mt_Chan4temp.n_vibratopos);
//    printf("%i %i %i %i ", mt_Chan4temp.n_tremolopos, mt_Chan4temp.n_pattpos, mt_Chan4temp.n_loopcount, mt_Chan4temp.n_wavecontrol);
//    printf("%i %i %i %i ", mt_Chan4temp.n_glissfunk, mt_Chan4temp.n_sampleoffset, mt_Chan4temp.n_toneportspeed, mt_Chan4temp.n_vibratocmd);
//    printf("%i %i %i %i ", mt_Chan4temp.n_tremolocmd, mt_Chan4temp.n_finetune, mt_Chan4temp.n_funkoffset, mt_Chan4temp.n_period);
//    printf("%i %i %i %i ", mt_Chan4temp.n_wantedperiod, mt_Chan4temp.n_length, mt_Chan4temp.n_replen, mt_Chan4temp.n_repend);
//    printf("%i %i %i %i ", ptr((const Byte*)AUD[3].DAT), ptr((const Byte*)AUD[3].REPDAT), AUD[3].TRIGGER, AUD[3].REPLEN);
//    printf("%i %i %f %f %f\n", AUD[3].POS, AUD[3].LEN, AUD[3].DELTA, AUD[3].FRAC, AUD[3].VOL);


            ++mt_Counter;
            if (mt_Counter >= mt_Speed) {
                mt_Counter = 0;

                if (mt_PattDelTime2 == 0) {
                    mt_PattPosOff = mt_PattOff + mt_PatternPos;

                    for (int i = 0; i < 4; ++i)
                        mt_Chan[i].mt_PlayVoice();
                    for (int i = 0; i < 4; ++i)
                        mt_Chan[i].setLoop();
                }
                else
                    checkEfx();

                mt_PatternPos += 16;

                if (mt_PattDelTime != 0) {
                    mt_PattDelTime2 = mt_PattDelTime;
                    mt_PattDelTime = 0;
                }

                if (mt_PattDelTime2 != 0) {
                    --mt_PattDelTime2;
                    if (mt_PattDelTime2 != 0)
                        mt_PatternPos -= 16;
                }

                if (mt_PBreakFlag) {
                    mt_PatternPos = mt_PBreakPos << 4;
                    mt_PBreakPos = 0;
                    mt_PBreakFlag = 0;
                }

                if ((mt_PatternPos >= 1024) || mt_PosJumpFlag)
                    mt_NextPosition();

                checkComplete();
            }
            else {
                checkEfx();
                if (mt_PosJumpFlag) {
                    mt_NextPosition();
                    checkComplete();
                }
            }

            switch (_mode) {
                case 0:
                    {
                        NoteDescriptor n = mt_Chan[0].noteDescriptor();
                        n.quantizeVolume(_volumeLevels);
                        float pos = mt_Chan[0].currentPosition();
                        int scanline = static_cast<int>(pos*n.period() / 228);
                        if (_notes.hasKey(n))
                            _notes[n].addScanlines(scanline);
                        else
                            _notes.add(n, NoteData(n, scanline, 262));
                        _song0.append(SongData0(n, scanline));
                    }
                    break;
                case 1:
                    {
                        SongData1 songData;
                        for (int i = 0; i < 4; ++i) {
                            NoteDescriptor n = mt_Chan[i].noteDescriptor();
                            n.quantizeVolume(_volumeLevels);
                            int per = n.period();
                            n.clearPeriod();
                            if (!_notes.hasKey(n))
                                _notes[n] = NoteData(n, 0, 256);
                            songData.setNoteDescriptor(i, n);
                            songData.setPeriod(i, per);
                        }
                        _song1.append(songData);
                    }
                    break;
                case 2:
                    {
                        // NYI
                        //for (int i = 0; i < 4; ++i) {
                        //    NoteDescriptor n = mt_Chan[i].noteDescriptor();
                        //    float pos = mt_Chan[i].currentPosition();
                        //    n.clearPeriod();
                        //    if (!_notes.hasKey(n))
                        //        _notes[n] = NoteData(n, pos, pos + );
                        //}
                    }
                    break;
            }

            //for (int i = 0; i < 4; ++i)
            //    mt_Chan[i].print();
            //printf("\n");

            for (int i = 0; i < 4; ++i)
                mt_Chan[i].advance(samplesPerFrame);

        } while (!_complete);

        console.write(String("Rendering to PIT data\n"));

        Array<Byte> waveData(0x10000);
        AppendableArray<Byte> songData;
        int nextPosition = 0;

        Array<float> spkrData;

        switch (_mode) {
            case 0:
                // NYI
                break;
            case 1:
                {
                    int cpuCyclesPerSample = 288;

                    int pitCyclesPerSample = cpuCyclesPerSample / 4;
                    int pitCyclesPerChannel = pitCyclesPerSample / 4;

                    int silentWave = 0;

                    // Output wave and song data
                    Array<Byte> waveBuffer(0x100);
                    for (int i = 0; i < _song1.count(); ++i) {
                        SongData1 s = _song1[i];
                        for (int channel = 0; channel < 4; ++channel) {
                            NoteDescriptor d = s.noteDescriptor(channel);
                            NoteData n = _notes[d];

                            int sample = d.sample();
                            Sample samp = _samples[sample];
                            int il = samp._repeatLength << 1;
                            if (n.offset() == -1) {
                                const Int8* data = samp._start + (samp._repeat << 1);
                                int v = d.amplitude();  // Range 0.._volumeLevels
                                if (nextPosition == 0x100)
                                    return false;
                                if (v == 0)
                                    silentWave = nextPosition >> 8;
                                for (int j = 0; j < 256; ++j) {
                                    int x = data[(j*il)/256];  // -128 to 127 inclusive
                                    float xx = x + 0.5;  // -127.5 to 127.5 inclusive
                                    xx = xx*v + 127.5*_volumeLevels; // 0 to 255*_volumeLevels
                                    x = (xx*pitCyclesPerChannel)/(255*_volumeLevels + 1);  // 0 to 17
                                    waveBuffer[j] = x + 1;
                                }
                                for (int j = 0; j < 256; ++j)
                                    waveData[nextPosition + (j << 8)] = waveBuffer[j];

                                _notes[d].setOffset(nextPosition);
                                ++nextPosition;
                                n = _notes[d];
                            }
                            songData.append(n.offset());
                            int period = s.period(channel);
                            float f = _amigaClock / (period * il);
                            f *= (11.0*3*cpuCyclesPerSample*65536)/157500000;
                            int velocity = static_cast<int>(f + 0.5);
                            songData.append(velocity & 0xff);
                            songData.append(velocity >> 8);
                        }
                        songData.append(0);
                        songData.append(0);
                        songData.append(0);
                        songData.append(0);
                    }

                    console.write(String("Samples used: ") + decimal(nextPosition) + "\n");

                    // Create waveform at 1.193MHz
                    int samplesPerV = 331;
                    spkrData.allocate(_song1.count()*samplesPerV*cpuCyclesPerSample / 4);

                    console.write(String("Song ticks: ") + decimal(_song1.count()) + "\n");

                    Array<Byte> pitData(_song1.count()*samplesPerV);
                    int pitP = 0;

                    int sample = 0;
                    UInt16 velocities[4];
                    UInt16 positions[4];
                    UInt8 waves[4];
                    for (int i = 0; i < 4; ++i) {
                        velocities[i] = 0;
                        waves[i] = silentWave;
                        positions[i] = 0;
                    }
                    int songPosition = 0;
                    for (int i = 0; i < spkrData.count(); i += pitCyclesPerSample) {
                        // The real player modifies one variable on each sample, so we'll do the same here.
                        switch (sample) {
                            case 0: waves[0] = songData[songPosition*16 + 0];                                               break;
                            case 1: velocities[0] = songData[songPosition*16 + 1] + (songData[songPosition*16 + 2] << 8);   break;
                            case 2: waves[1] = songData[songPosition*16 + 3];                                               break;
                            case 3: velocities[1] = songData[songPosition*16 + 4] + (songData[songPosition*16 + 5] << 8);   break;
                            case 4: waves[2] = songData[songPosition*16 + 6];                                               break;
                            case 5: velocities[2] = songData[songPosition*16 + 7] + (songData[songPosition*16 + 8] << 8);   break;
                            case 6: waves[3] = songData[songPosition*16 + 9];                                               break;
                            case 7: velocities[3] = songData[songPosition*16 + 10] + (songData[songPosition*16 + 11] << 8); break;
                        }
                        ++sample;
                        if (sample == samplesPerV) {
                            ++songPosition;
                            sample = 0;
                            if (songPosition%50 == 0)
                                console.write(".");
                        }
                        int pit = 0;
                        for (int j = 0; j < 4; ++j) {
                            //if (waves[j] >= 121)
                            //    waves[j] = 120;
                            positions[j] += velocities[j];
                            UInt16 x = (waves[j] & 0xff) | (positions[j] & 0xff00);
                            int v = waveData[x];
                            //if (v <= 0 || v > 18)
                            //    console.write(String("Bad PIT value\n"));
                            pit += v;
                        }
                        //if (pit <= 0 || pit > 72)
                        //    console.write(String("Bad PIT value\n"));
                        if (pit == 0)
                            console.write(String("Bad PIT value\n"));
                        for (int j = 0; j < pitCyclesPerSample; ++j)
                            spkrData[i + j] = (j < pit ? 1 : -1);

                        pitData[pitP] = pit;
                        ++pitP;
                    }
                    //console.write(String("pitP: ") + decimal(pitP) + "\n");

                    FileHandle out = File(_inputFileName + "_out.pcm").openWrite();
                    out.write(pitData);

                    console.write("\n");
                }
                break;
            case 2:
                // NYI
                break;
        }

        // Output data for playback routine
        File outputFile(_inputFileName + "_out.dat");
        FileHandle out = outputFile.openWrite();
        out.write(waveData);
        out.write(songData);

        console.write(String("Resampling\n"));

        // Resample to a sensible depth
        double ratio = _wavSampleRate*11.0/13125000;
        int outputSize = static_cast<int>(spkrData.count() * ratio);
        Array<float> waveFloat(outputSize);

        SRC_DATA data;
        data.data_in = &spkrData[0];
        data.input_frames = spkrData.count();
        data.data_out = &waveFloat[0];
        data.output_frames = outputSize;
        data.src_ratio = ratio;
        //int src_result = src_simple(&data, SRC_SINC_BEST_QUALITY, 1);
        int src_result = src_simple(&data, SRC_SINC_FASTEST, 1);

        // Normalize
        float normalization = 0;
        for (int i = 0; i < outputSize; ++i) {
            float f = waveFloat[i];
            if (f > normalization)
                normalization = f;
            else
                if (f < -normalization)
                    normalization = -f;
        }
        Array<Int16> waveInt(outputSize);
        for (int i = 0; i < outputSize; ++i) {
            int wi = static_cast<int>(32768.0*waveFloat[i]/normalization);
            if (wi > 32767)
                wi = 32767;
            if (wi < -32768)
                wi = -32768;
            waveInt[i] = wi;
        }

        console.write(String("Writing WAV\n"));

        // Output
        WAVEFORMATEX format;
        ZeroMemory(&format, sizeof(WAVEFORMATEX));
        format.wFormatTag = WAVE_FORMAT_PCM;
        format.nChannels = 1;
        format.nSamplesPerSec = _wavSampleRate;
        int nBlockAlign = sizeof(Int16);
        format.nAvgBytesPerSec = _wavSampleRate*nBlockAlign;
        format.nBlockAlign = nBlockAlign;
        format.wBitsPerSample = sizeof(Int16)*8;
        format.cbSize = 0;

        FileHandle handle = File(_inputFileName + "_out.wav").openWrite();
        handle.write("RIFF", 4);
        DWORD t = 36 + 2*outputSize;
        handle.write(&t, 4);
        handle.write("WAVE", 4);
        handle.write("fmt ", 4);
        t = 16;
        handle.write(&t, 4);
        handle.write(&format, 16);
        handle.write("data", 4);
        t = 2*outputSize;
        handle.write(&t, 4);
        handle.write(waveInt);

        console.write(String("Complete\n"));

        return true;
    }

private:
    class PT_CHN
    {
    public:
        PT_CHN()
          : n_note(0), n_cmd(0), n_start(0), n_wavestart(0), n_loopstart(0),
          n_volume(0), n_toneportdirec(0), n_vibratopos(0), n_tremolopos(0),
          n_pattpos(0), n_loopcount(0), n_wavecontrol(0), n_glissfunk(0),
          n_sampleoffset(0), n_toneportspeed(0), n_vibratocmd(0),
          n_tremolocmd(0), n_finetune(0), n_funkoffset(0), n_period(0),
          n_wantedperiod(0), n_length(0), n_replen(0), n_repend(0), DAT(0),
          REPDAT(0), TRIGGER(false), REPLEN(0), POS(0), LEN(0), DELTA(0),
          FRAC(0), VOL(0) { }

        void init(ModPlayer* modPlayer) { _modPlayer = modPlayer; }

        void mt_CheckEfx()
        {
            mt_UpdateFunk();

            if ((n_cmd & 0x0FFF) == 0) {
                mt_PaulaSetPer(n_period);
                return;
            }
            switch (commandMajor()) {
                case commandArpeggio:
                    {
                        UInt8 dat = _modPlayer->mt_Counter % 3;
                        if (dat == 0)
                            mt_PaulaSetPer(n_period);
                        else {
                            if (dat == 1)
                                dat = (n_cmd & 0x00FF) >> 4;
                            else if (dat == 2)
                                dat = n_cmd & 0x000F;
                            mt_PaulaSetPer(tunePeriod(n_period, dat));
                        }
                    }
                    break;
                case commandPortaUp:
                    mt_PortaUp();
                    break;
                case commandPortaDown:
                    mt_PortaDown();
                    break;
                case commandTonePortamento:
                    if (n_cmd & 0x00FF) {
                        n_toneportspeed = n_cmd & 0x00FF;
                        n_cmd &= 0xFF00;
                    }
                    mt_TonePortNoChange();
                    break;
                case commandVibrato:
                    if (z() != 0) {
                        if (y() != 0)
                            n_vibratocmd = (n_vibratocmd & 0xF0) | y();

                        if (x() != 0)
                            n_vibratocmd = (x() << 4) | (n_vibratocmd & 0x0F);
                    }
                    mt_VibratoNoChange();
                    break;
                case commandTonePlusVolSlide:
                    mt_TonePortNoChange();
                    mt_VolumeSlide();
                    break;
                case commandVibratoPlusVolSlide:
                    mt_VibratoNoChange();
                    mt_VolumeSlide();
                    break;
                case commandECommands:
                    mt_E_Commands();
                    break;
                case commandTremolo:
                    mt_PaulaSetPer(n_period);
                    {
                        if (z() != 0) {
                            if (y() != 0)
                                n_tremolocmd = (n_tremolocmd & 0xF0) | y();

                            if (x() != 0)
                                n_tremolocmd = (x() << 4) | (n_tremolocmd & 0x0F);
                        }

                        Int8 tremoloTemp = (n_tremolopos >> 2) & 0x1F;
                        Int16 tremoloData = (n_wavecontrol >> 4) & 0x03;

                        if (tremoloData == 0)
                            tremoloData = mt_VibratoTable[tremoloTemp];
                        else  {
                            if (tremoloData == 1) {
                                if (n_vibratopos < 0) /* PT bug, but don't fix this one */
                                    tremoloData = 255 - (tremoloTemp << 3);
                                else
                                    tremoloData = tremoloTemp << 3;
                            }
                            else
                                tremoloData = 255;
                        }

                        tremoloData = (tremoloData * (n_tremolocmd & 0x0F)) >> 6;

                        if (n_tremolopos < 0)
                            tremoloData = max(n_volume - tremoloData, 0);
                        else
                            tremoloData = min(n_volume + tremoloData, 64);
                        mt_PaulaSetVol(tremoloData);

                        n_tremolopos += ((n_tremolocmd >> 2) & 0x3C);
                    }
                    break;
                case commandVolumeSlide:
                    mt_PaulaSetPer(n_period);
                    mt_VolumeSlide();
                    break;

                default:
                    mt_PaulaSetPer(n_period);
                    break;
            }
        }

        void mt_PlayVoice()
        {
            if (n_note == 0 && n_cmd == 0) /* no channel data on this row */
                mt_PaulaSetPer(n_period);

            const UInt8* pattData =
                &_modPlayer->mt_SongDataPtr[_modPlayer->mt_PattPosOff];

            _modPlayer->mt_PattPosOff += 4;

            n_note  = (pattData[0] << 8) | pattData[1];
            n_cmd   = (pattData[2] << 8) | pattData[3];

            UInt8 sample = (pattData[0] & 0xF0) | ((pattData[2] & 0xF0) >> 4);
            // BUGFIX: don't do samples >31
            if (sample != 0 && (sample <= 32)) {
                Sample s = _modPlayer->_samples[sample - 1];
                n_start = s._start;
                n_finetune = s._fineTune;
                n_volume = s._volume;
                n_length = s._length;
                n_replen = s._repeatLength;
                _sample = sample - 1;
                UInt16 repeat = s._repeat;
                if (repeat > 0) {
                    n_loopstart = n_start + (repeat << 1);
                    n_wavestart = n_loopstart;
                    n_length    = repeat + n_replen;
                }
                else {
                    n_loopstart = n_start;
                    n_wavestart = n_start;
                }
            }

            if ((n_note & 0x0FFF) == 0) {
                mt_CheckMoreEfx();
                mt_PaulaSetVol(n_volume);
                return;
            }
            if (command() == commandSetFineTune)
                mt_SetFineTune();
            else {
                if (commandMajor() == commandTonePortamento ||
                    commandMajor() == commandTonePlusVolSlide) {
                    // SetTonePorta
                    n_wantedperiod = tunePeriod(n_note & 0x0FFF, 0, true);
                    n_toneportdirec = 0;
                    if (n_period == n_wantedperiod)
                        n_wantedperiod = 0;
                    else
                        if (n_period > n_wantedperiod)
                            n_toneportdirec = 1;
                    mt_CheckMoreEfx();
                    mt_PaulaSetVol(n_volume);
                    return;
                }
                if (commandMajor() == commandSampleOffset)
                    mt_CheckMoreEfx();
            }
            mt_SetPeriod();
            mt_PaulaSetVol(n_volume);
        }

        void setLoop() { mt_PaulaSetLoop(n_loopstart, n_replen); }

        void mix(int numSamples)
        {
            if (!TRIGGER || DAT == 0)
                return;
            for (int j = 0; j < numSamples; ++j) {
                _modPlayer->masterBuffer[j] += DAT[POS]*VOL;

                FRAC += DELTA;
                if (FRAC >= 1.0f) {
                    POS  += (Int32)(FRAC);
                    FRAC -= (Int32)(FRAC);

                    if (POS >= LEN) {
                        if (REPLEN > 2) {
                            DAT  = REPDAT;
                            POS -= LEN;
                            LEN  = REPLEN;
                        }
                        else {
                            POS     = 0;
                            TRIGGER = false;
                            break;
                        }
                    }
                }
            }
        }
        void advance(int numSamples)
        {
            if (!TRIGGER || DAT == 0)
                return;
            FRAC += DELTA*numSamples;
            if (FRAC >= 1.0f) {
                POS  += (Int32)(FRAC);
                FRAC -= (Int32)(FRAC);

                if (POS >= LEN) {
                    if (REPLEN > 2) {
                        DAT  = REPDAT;
                        POS -= LEN;
                        LEN  = REPLEN;
                        POS %= LEN;
                    }
                    else {
                        POS     = 0;
                        TRIGGER = false;
                    }
                }
            }
        }
        int ptr(const Int8* p)
        {
            if (p == 0)
                return 0;
            return p - reinterpret_cast<const Int8*>(_modPlayer->mt_SongDataPtr);
        }
        NoteDescriptor noteDescriptor()
        {
            return NoteDescriptor(_sample, _period, (TRIGGER && (DAT != 0)) ? VOL : 0);
        }
        int loopCount() const { return n_loopcount; }
        //void print()
        //{
        //    printf("%01i %04x %04x %03i %03i %02i %03i %03i  ", TRIGGER, ptr(DAT), ptr(REPDAT), REPLEN, LEN, VOL, _period, POS);
        //}
        float currentPosition() const { return FRAC + POS + (DAT - n_start); }
    private:
        void mt_PaulaStart() { POS = 0; FRAC = 0.0f; TRIGGER = true; }
        void mt_PaulaSetVol(int vol) { VOL = vol; }
        void mt_PaulaSetLen(int len) { LEN = len << 1; }
        void mt_PaulaSetDat(const Int8* dat) { DAT = dat; }
        void mt_PaulaSetLoop(const Int8* loopstart, int replen)
        {
            if (loopstart != 0)
                REPDAT = loopstart;
            REPLEN = replen << 1;
        }
        void mt_PaulaSetPer(int per)
        {
            _period = per;
            if (per != 0)
                DELTA = (_modPlayer->_amigaClock/per)/_modPlayer->f_outputFreq;
        }

        void mt_UpdateFunk()
        {
            if ((n_glissfunk >> 4) != 0) {
                static const UInt8 mt_FunkTable[16] = {
                    0x00, 0x05, 0x06, 0x07, 0x08, 0x0A, 0x0B, 0x0D,
                    0x0F, 0x13, 0x16, 0x1A, 0x20, 0x2B, 0x40, 0x80 };

                n_funkoffset += mt_FunkTable[n_glissfunk >> 4];
                if ((n_funkoffset & 128) != 0) {
                    n_funkoffset = 0;

                    if (n_wavestart) { /* added for safety reasons */
                        if (++n_wavestart >= (n_loopstart + n_replen))
                            n_wavestart = n_loopstart;

                        *const_cast<Int8*>(n_wavestart) = -1 - *n_wavestart;
                    }
                }
            }
        }

        void mt_SetFineTune()  // E 5
        {
            n_finetune = y();
        }

        void mt_VolumeSlide()  // A
        {
            if (x() == 0)
                n_volume = max(n_volume - y(), 0);
            else
                n_volume = min(n_volume + x(), 64);

            mt_PaulaSetVol(n_volume);
        }

        void mt_PortaUp()  // 1
        {
            n_period -= (z() & _modPlayer->mt_LowMask);
            _modPlayer->mt_LowMask = 0xFF;

            if ((n_period & 0x0FFF) < 113) {
                n_period &= 0xF000;
                n_period |= 113;
            }

            mt_PaulaSetPer(n_period & 0x0FFF);
        }

        void mt_PortaDown()  // 2
        {
            n_period += (z() & _modPlayer->mt_LowMask);
            _modPlayer->mt_LowMask = 0xFF;

            if ((n_period & 0x0FFF) > 856) {
                n_period &= 0xF000;
                n_period |= 856;
            }

            mt_PaulaSetPer(n_period & 0x0FFF);
        }

        void mt_TonePortNoChange()
        {
            if (n_wantedperiod) {
                if (n_toneportdirec) {
                    n_period -= n_toneportspeed;
                    if (n_period <= n_wantedperiod) {
                        n_period = n_wantedperiod;
                        n_wantedperiod = 0;
                    }
                }
                else {
                    n_period += n_toneportspeed;
                    if (n_period >= n_wantedperiod) {
                        n_period = n_wantedperiod;
                        n_wantedperiod = 0;
                    }
                }

                if ((n_glissfunk & 0x0F) == 0)
                    mt_PaulaSetPer(n_period);
                else
                    mt_PaulaSetPer(tunePeriod(n_period));
            }
        }

        void mt_VibratoNoChange()
        {
            UInt8 vibratoTemp = (n_vibratopos >> 2) & 0x1F;
            Int16 vibratoData =  n_wavecontrol      & 0x03;

            //printf("%i %i %i\n",vibratoTemp, vibratoData,n_vibratocmd);

            if (vibratoData == 0)
                vibratoData = mt_VibratoTable[vibratoTemp];
            else {
                if (vibratoData == 1) {
                    if (n_vibratopos < 0)
                        vibratoData = 255 - (vibratoTemp << 3);
                    else
                        vibratoData = vibratoTemp << 3;
                }
                else
                    vibratoData = 255;
            }

            vibratoData = (vibratoData * (n_vibratocmd & 0x0F)) >> 7;

            if (n_vibratopos < 0)
                vibratoData = n_period - vibratoData;
            else
                vibratoData = n_period + vibratoData;

            mt_PaulaSetPer(vibratoData);

            n_vibratopos += ((n_vibratocmd >> 2) & 0x3C);
        }

        void mt_E_Commands()  // E
        {
            switch (command()) {
                case commandFilter:
                    break;
                case commandFinePortaUp:
                    if (_modPlayer->mt_Counter != 0)
                        break;
                    _modPlayer->mt_LowMask = 0x0F;
                    mt_PortaUp();
                    break;
                case commandFinePortaDown:
                    if (_modPlayer->mt_Counter != 0)
                        break;
                    _modPlayer->mt_LowMask = 0x0F;
                    mt_PortaDown();
                    break;
                case commandSetGlissControl:
                    n_glissfunk = (n_glissfunk & 0xF0) | y();
                    break;
                case commandSetVibratoControl:
                    n_wavecontrol = (n_wavecontrol & 0xF0) | y();
                    break;
                case commandSetFineTune:
                    mt_SetFineTune();
                    break;
                case commandJumpLoop:
                    if (_modPlayer->mt_Counter != 0)
                        break;
                    if (y() == 0)
                        n_pattpos = (Int8)(_modPlayer->mt_PatternPos >> 4);
                    else {
                        if (n_loopcount == 0)
                            n_loopcount = y();
                        else {
                            --n_loopcount;
                            if (n_loopcount == 0)
                                break;
                        }

                        _modPlayer->mt_PBreakPos  = n_pattpos;
                        _modPlayer->mt_PBreakFlag = 1;
                    }
                    break;
                case commandSetTremoloControl:
                    n_wavecontrol = (n_wavecontrol & 0x0F) | (y() << 4);
                    break;
                case commandRetrigNote:
                    if (y() == 0)
                        break;
                    if (_modPlayer->mt_Counter == 0)
                        if ((n_note & 0x0FFF) != 0)
                            break;

                    if ((_modPlayer->mt_Counter % y()) == 0) {
                        mt_PaulaSetDat(n_start);
                        mt_PaulaSetLen(n_length);
                        mt_PaulaSetLoop(n_loopstart, n_replen);
                        mt_PaulaStart();
                    }

                    break;
                case commandVolumeFineUp:
                    if (_modPlayer->mt_Counter != 0)
                        break;
                    n_volume = min(n_volume + y(), 64);
                    mt_PaulaSetVol(n_volume);
                    break;
                case commandVolumeFineDown:
                    if (_modPlayer->mt_Counter != 0)
                        break;
                    n_volume = max(n_volume - y(), 0);
                    mt_PaulaSetVol(n_volume);
                    break;
                case commandNoteCut:
                    if (_modPlayer->mt_Counter != y())
                        break;
                    n_volume = 0;
                    mt_PaulaSetVol(0);
                    break;
                case commandNoteDelay:
                    if (_modPlayer->mt_Counter != y())
                        break;
                    if (n_note != 0) {
                        mt_PaulaSetDat(n_start);
                        mt_PaulaSetLen(n_length);
                        mt_PaulaSetLoop(n_loopstart, n_replen);
                        mt_PaulaStart();
                    }
                    break;
                case commandPatternDelay:
                    if (_modPlayer->mt_Counter == 0 &&
                        _modPlayer->mt_PattDelTime2 == 0)
                        _modPlayer->mt_PattDelTime = y() + 1;
                    break;
                case commandFunkIt:
                    if (_modPlayer->mt_Counter != 0)
                        break;
                    n_glissfunk = (y() << 4) | (n_glissfunk & 0x0F);

                    if ((n_glissfunk & 0xF0) != 0)
                        mt_UpdateFunk();
                    break;
            }
        }

        void mt_CheckMoreEfx()
        {
            mt_UpdateFunk();

            switch (commandMajor()) {
                case commandSampleOffset:
                    {
                        if (z() != 0)
                            n_sampleoffset = z();
                        UInt16 newOffset = n_sampleoffset << 7;
                        if (newOffset < n_length) {
                            n_length -=  newOffset;
                            n_start += (newOffset << 1);
                        }
                        else
                            n_length = 1;
                    }
                    break;
                case commandPositionJump:
                    _modPlayer->mt_SongPos = z() - 1; /* 0xFF (B00) jumps to pat 0 */
                    _modPlayer->mt_PBreakPos = 0;
                    _modPlayer->mt_PosJumpFlag = 1;
                    break;
                case commandPatternBreak:
                    _modPlayer->mt_PBreakPos = (x() * 10) + y();
                    if (_modPlayer->mt_PBreakPos > 63)
                        _modPlayer->mt_PBreakPos = 0;
                    _modPlayer->mt_PosJumpFlag = 1;
                    break;
                case commandECommands:
                    mt_E_Commands();
                    break;
                case commandSetSpeed:
                    if (z() == 0)
                        break;
                    _modPlayer->mt_Counter = 0;
                    if (_modPlayer->mt_TempoMode || (z() < 32))
                        _modPlayer->mt_Speed = z();
                    else
                        _modPlayer->samplesPerFrame =
                            (Int16)(_modPlayer->mt_TimerVal / z());
                    break;
                case commandVolumeChange:
                    n_volume = min(z(), 64);
                    mt_PaulaSetVol(n_volume);
                    break;
                default:
                    mt_PaulaSetPer(n_period); break;
            }
        }

        void mt_SetPeriod()
        {
            n_period = tunePeriod(n_note & 0x0FFF);
            if (command() != commandNoteDelay) {
                if ((n_wavecontrol & 0x04) == 0)
                    n_vibratopos = 0;
                if ((n_wavecontrol & 0x40) == 0)
                    n_tremolopos = 0;

                mt_PaulaSetDat(n_start);
                mt_PaulaSetLen(n_length);
                mt_PaulaSetPer(n_period);
                mt_PaulaStart();
            }

            mt_CheckMoreEfx();
        }

        int tunePeriod(int period, int offset = 0, bool tonePorta = false)
        {
            if (_modPlayer->_noClamp) {
                float aPeriod = (157500000.0/(11*4*440*16));  // == 508
                static const int fineTunes[16] = {0, -1, -2, -3, -4, -5, -6, -7, 8, 7, 6, 5, 4, 3, 2, 1};

                //    tableValue[i] = aPeriod * pow(2, (72 + fineTunes[n_finetune] - i*8)/96.0);

                int i = static_cast<int>(((72 + fineTunes[n_finetune]) - 96*log(period/aPeriod)/log(2.0))/8 + 0.5);

                if (tonePorta && ((n_finetune & 8) != 0) && (i != 0))
                    --i;

                i += offset;

                return static_cast<int>(aPeriod * pow(2, (72 + fineTunes[n_finetune] - i*8)/96.0) + 0.5);
            }
            static const Int16 mt_PeriodTable[] = {
            //  C    C#   D    D#   E    F    F#   G    G#   A    A#   B    C    C#   D    D#   E    F    F#   G    G#   A    A#   B    C    C#   D    D#   E    F    F#   G    G#   A    A#   B
                856, 808, 762, 720, 678, 640, 604, 570, 538, 508, 480, 453, 428, 404, 381, 360, 339, 320, 302, 285, 269, 254, 240, 226, 214, 202, 190, 180, 170, 160, 151, 143, 135, 127, 120, 113,
                850, 802, 757, 715, 674, 637, 601, 567, 535, 505, 477, 450, 425, 401, 379, 357, 337, 318, 300, 284, 268, 253, 239, 225, 213, 201, 189, 179, 169, 159, 150, 142, 134, 126, 119, 113,
                844, 796, 752, 709, 670, 632, 597, 563, 532, 502, 474, 447, 422, 398, 376, 355, 335, 316, 298, 282, 266, 251, 237, 224, 211, 199, 188, 177, 167, 158, 149, 141, 133, 125, 118, 112,
                838, 791, 746, 704, 665, 628, 592, 559, 528, 498, 470, 444, 419, 395, 373, 352, 332, 314, 296, 280, 264, 249, 235, 222, 209, 198, 187, 176, 166, 157, 148, 140, 132, 125, 118, 111,
                832, 785, 741, 699, 660, 623, 588, 555, 524, 495, 467, 441, 416, 392, 370, 350, 330, 312, 294, 278, 262, 247, 233, 220, 208, 196, 185, 175, 165, 156, 147, 139, 131, 124, 117, 110,
                826, 779, 736, 694, 655, 619, 584, 551, 520, 491, 463, 437, 413, 390, 368, 347, 328, 309, 292, 276, 260, 245, 232, 219, 206, 195, 184, 174, 164, 155, 146, 138, 130, 123, 116, 109,
                820, 774, 730, 689, 651, 614, 580, 547, 516, 487, 460, 434, 410, 387, 365, 345, 325, 307, 290, 274, 258, 244, 230, 217, 205, 193, 183, 172, 163, 154, 145, 137, 129, 122, 115, 109,
                814, 768, 725, 684, 646, 610, 575, 543, 513, 484, 457, 431, 407, 384, 363, 342, 323, 305, 288, 272, 256, 242, 228, 216, 204, 192, 181, 171, 161, 152, 144, 136, 128, 121, 114, 108,
                907, 856, 808, 762, 720, 678, 640, 604, 570, 538, 508, 480, 453, 428, 404, 381, 360, 339, 320, 302, 285, 269, 254, 240, 226, 214, 202, 190, 180, 170, 160, 151, 143, 135, 127, 120,
                900, 850, 802, 757, 715, 675, 636, 601, 567, 535, 505, 477, 450, 425, 401, 379, 357, 337, 318, 300, 284, 268, 253, 238, 225, 212, 200, 189, 179, 169, 159, 150, 142, 134, 126, 119,
                894, 844, 796, 752, 709, 670, 632, 597, 563, 532, 502, 474, 447, 422, 398, 376, 355, 335, 316, 298, 282, 266, 251, 237, 223, 211, 199, 188, 177, 167, 158, 149, 141, 133, 125, 118,
                887, 838, 791, 746, 704, 665, 628, 592, 559, 528, 498, 470, 444, 419, 395, 373, 352, 332, 314, 296, 280, 264, 249, 235, 222, 209, 198, 187, 176, 166, 157, 148, 140, 132, 125, 118,
                881, 832, 785, 741, 699, 660, 623, 588, 555, 524, 494, 467, 441, 416, 392, 370, 350, 330, 312, 294, 278, 262, 247, 233, 220, 208, 196, 185, 175, 165, 156, 147, 139, 131, 123, 117,
                875, 826, 779, 736, 694, 655, 619, 584, 551, 520, 491, 463, 437, 413, 390, 368, 347, 328, 309, 292, 276, 260, 245, 232, 219, 206, 195, 184, 174, 164, 155, 146, 138, 130, 123, 116,
                868, 820, 774, 730, 689, 651, 614, 580, 547, 516, 487, 460, 434, 410, 387, 365, 345, 325, 307, 290, 274, 258, 244, 230, 217, 205, 193, 183, 172, 163, 154, 145, 137, 129, 122, 115,
                862, 814, 768, 725, 684, 646, 610, 575, 543, 513, 484, 457, 431, 407, 384, 363, 342, 323, 305, 288, 272, 256, 242, 228, 216, 203, 192, 181, 171, 161, 152, 144, 136, 128, 121, 114 };

            const Int16* portaPointer = &mt_PeriodTable[36 * n_finetune];
            int i;
            for (i = 0; i < 35; ++i)
                if (period >= portaPointer[i])
                    break;
            if (tonePorta && ((n_finetune & 8) != 0) && (i != 0))
                --i;
            return portaPointer[i + offset];
        }
        int commandMajor() { return n_cmd & 0xf00; }
        int command() { return n_cmd & 0xff0; }
        int x() { return (n_cmd & 0xf0) >> 4; }
        int y() { return n_cmd & 0xf; }
        int z() { return n_cmd & 0xff; }

        ModPlayer* _modPlayer;
        Int16 n_note;
        UInt16 n_cmd;
        const Int8* n_start;
        const Int8* n_wavestart;
        const Int8* n_loopstart;
        Int8 n_volume;
        Int8 n_toneportdirec;
        Int8 n_vibratopos;
        Int8 n_tremolopos;
        Int8 n_pattpos;
        Int8 n_loopcount;
        UInt8 n_wavecontrol;
        UInt8 n_glissfunk;
        UInt8 n_sampleoffset;
        UInt8 n_toneportspeed;
        UInt8 n_vibratocmd;
        UInt8 n_tremolocmd;
        UInt8 n_finetune;
        UInt8 n_funkoffset;
        Int16 n_period;
        Int16 n_wantedperiod;
        UInt32 n_length;
        UInt32 n_replen;
        UInt32 n_repend;

        const Int8* DAT;
        const Int8* REPDAT;
        bool TRIGGER;

        UInt32 REPLEN;
        UInt32 POS;
        UInt32 LEN;

        float DELTA;
        int _period;
        float FRAC;
        int VOL;

        int _sample;
    };

    void mt_NextPosition(void)
    {
        mt_PatternPos  = (UInt16)(mt_PBreakPos) << 4;
        mt_PBreakPos   = 0;
        mt_PosJumpFlag = 0;

        mt_SongPos = (mt_SongPos + 1) & 0x7F;
        if (mt_SongPos >= mt_SongDataPtr[950])
            mt_SongPos = 0;

        mt_PattOff = 1084 + ((UInt32)(mt_SongDataPtr[952 + mt_SongPos]) << 10);
    }

    void checkEfx()
    {
        for (int i = 0; i < 4; ++i)
            mt_Chan[i].mt_CheckEfx();
    }

    PT_CHN mt_Chan[4];

    class Sample
    {
    public:
        Sample() { }
        Sample(const Int8* start, const Byte* data) : _start(start)
        {
            _fineTune = data[2] & 0xf;
            _volume = data[3];
            _length = (data[0] << 8) | data[1];
            _repeat = (data[4] << 8) | data[5];
            _repeatLength = (data[6] << 8) | data[7];
        }
        const Int8* _start;
        int _length;
        int _fineTune;
        int _volume;
        int _repeat;
        int _repeatLength;
    };

    class NoteData
    {
    public:
        NoteData() {}
        NoteData(NoteDescriptor noteDescriptor, int scanline, int length)
          : _noteDescriptor(noteDescriptor), _beginByte(scanline),
            _endByte(scanline + length), _offset(-1) { }
        void addScanlines(int scanline)
        {
            if (scanline < _beginByte)
                _beginByte = scanline;
            else
                if (scanline + 262 > _endByte)
                    _endByte = scanline + 262;
        }
        int length() const { return _endByte - _beginByte; }
        int offset() const { return _offset; }
        void setOffset(int offset) { _offset = offset; }
    private:
        NoteDescriptor _noteDescriptor;
        int _beginByte;
        int _endByte;
        int _offset;
    };

    class SongData0
    {
    public:
        SongData0(NoteDescriptor noteDescriptor, int pos)
            : _noteDescriptor(noteDescriptor), _pos(pos) { }
        NoteDescriptor noteDescriptor() const { return _noteDescriptor; }
        int pos() const { return _pos; }
    private:
        NoteDescriptor _noteDescriptor;
        int _pos;
    };

    class SongData1
    {
    public:
        void setNoteDescriptor(int channel, NoteDescriptor noteDescriptor)
        {
            _noteDescriptors[channel] = noteDescriptor;
        }
        NoteDescriptor noteDescriptor(int channel) const
        {
            return _noteDescriptors[channel];
        }
        void setPeriod(int channel, int period)
        {
            _periods[channel] = period;
        }
        int period(int channel) const { return _periods[channel]; }
    private:
        NoteDescriptor _noteDescriptors[4];
        int _periods[4];
    };

    Sample _samples[31];

    Int8 mt_TempoMode;
    Int8 mt_SongPos;
    Int8 mt_PosJumpFlag;
    Int8 mt_PBreakFlag;
    Int8 mt_PBreakPos;
    Int8 mt_PattDelTime;
    Int8 mt_PattDelTime2;
    const UInt8* mt_SongDataPtr;
    UInt8 mt_LowMask;
    UInt8 mt_Counter;
    UInt8 mt_Speed;
    UInt16 mt_PatternPos;
    UInt32 mt_TimerVal;
    UInt32 mt_PattPosOff;
    UInt32 mt_PattOff;
    float f_outputFreq;
    Array<Int16> masterBuffer;
    int samplesPerFrame;
    float _amigaClock;
    int _volumeLevels;
    bool _noClamp;

    void produce(int n)
    {

        Accessor<Int16> w = writer(samplesPerFrame);
        int numSamples = samplesPerFrame;
        memset(&masterBuffer[0], 0, sizeof (Int16) * samplesPerFrame);

        for (int i = 0; i < 4; ++i)
            mt_Chan[i].mix(samplesPerFrame);

        for (int j = 0; j < samplesPerFrame; ++j)
            w.item() = masterBuffer[j];
        written(samplesPerFrame);
    }

    int _mode;
    int _wavSampleRate;
    float _pcSampleRate;
    bool _complete;
    HashTable<NoteDescriptor, NoteData> _notes;
    AppendableArray<SongData0> _song0;
    AppendableArray<SongData1> _song1;
    Set<int> _phases;
    String _inputFileName;
};


class Program : public ProgramBase
{
public:
    void run()
    {
        int mode;
        bool parsed = false;
        if (_arguments.count() >= 3) {
            CharacterSource source(_arguments[2]);
            Space::parse(&source);
            Span span;
            parsed = Space::parseInteger(&source, &mode, &span);
            CharacterSource s = source;
            if (s.get() != -1)
                source.location().throwError("Expected end of string");
        }
        if (!parsed) {
            console.write("Syntax: " + _arguments[0] +
                " <MOD file name> <mode> [/noclamp]\n"
                "Modes are: \n"
                "  0 for VIC (1 channel, sample point per scanline, update "
                "per frame,\n"
                "    262 sample points per frame, 76 levels, 59.92Hz tick "
                "rate).\n"
                "  1 for SID (4 channels, 256-point samples, 65536 "
                "frequencies).\n"
                "  2 for Paula (4 channels, 256 frequencies).\n");
            return;
        }
        bool noClamp = false;
        if (_arguments.count() >= 4)
            if (_arguments[3] == "/noclamp")
                noClamp = true;

        String inputFileName = _arguments[1];
        Array<Byte> modData;
        File(inputFileName, true).readIntoArray<Byte>(&modData);

        int i;
        for (i = inputFileName.length() - 1; i >= 0; --i)
            if (inputFileName[i] == '.')
                break;
        if (i != -1)
            inputFileName = inputFileName.subString(0, i);
        String outputFileName = inputFileName + "_out.wav";

        int sampleRate = 44100;

        for (int volumes = 64; volumes >= 1; --volumes) {
            ModPlayer player(&modData[0], sampleRate, mode, volumes, inputFileName, noClamp);
            bool result = player.calculate();
            if (result) {
                console.write(String("Succeeded with ") + decimal(volumes) + " volume levels.\n");
                //WaveFileSink<Int16> sink(File(outputFileName, true), sampleRate);
                //player.connect(&sink);
                //sink.play();
                return;
            }
        }
        console.write(String("Too much waveform data - reduce size/number of samples.\n"));

    }
};
