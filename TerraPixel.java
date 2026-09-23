
import java.awt.*;
import java.awt.event.*;
import java.awt.image.BufferedImage;
import java.io.*;
import java.net.*;
import java.util.*;
import java.util.List;
import java.util.concurrent.*;
import java.util.zip.*;
import javax.imageio.ImageIO;
import javax.sound.sampled.*;
import javax.swing.*;
import javax.swing.filechooser.FileNameExtensionFilter;

public class TerraPixel extends JPanel implements ActionListener, KeyListener,
        MouseListener, MouseMotionListener, MouseWheelListener {

    // ==================== КОНСТАНТЫ ====================
    public static final String VERSION = "1.0.0 \"Faithful\"";
    public static final String GAME_TITLE = "TerraPixel";

    public static final int TILE = 32;
    public static final int VIEW_W = 30;
    public static final int VIEW_H = 20;
    public static final int SCREEN_W = TILE * VIEW_W;
    public static final int SCREEN_H = TILE * VIEW_H;

    public static final int INV_COLS = 9;
    public static final int INV_ROWS = 4;
    public static final int SLOT = 44;
    public static final int ARMOR_SLOTS = 4;
    public static final int CRAFT_SIZE = 9;

    public static final int DEFAULT_WORLD_W = 800;
    public static final int DEFAULT_WORLD_H = 200;
    public static final int DAY_LENGTH = 60 * 60 * 3;
    public static final int MP_PORT = 25565;

    // ==================== ENUM ====================
    enum GameState {
        MENU, WORLD_SELECT, WORLD_CREATE, PLAYING, PAUSED, DEAD,
        ACHIEVEMENTS, SETTINGS, MULTIPLAYER, MP_HOST_WAITING, LOADING,
        RESOURCEPACKS, TRADE
    }

    enum GameMode {
        SURVIVAL, CREATIVE, HARDCORE
    }

    enum WorldType {
        NORMAL("Обычный"), NETHER("Ад"), HEAVEN("Рай"),
        CAVE("Пещерный"), OCEAN("Океан"), WASTELAND("Пустошь"),
        SNOWY("Снежный"), JUNGLE("Джунгли"), FLAT("Плоский");
        final String displayName;

        WorldType(String n) {
            displayName = n;
        }
    }

    enum Biome {
        FOREST, DESERT, SNOWY, JUNGLE, OCEAN, WASTELAND, NETHER, HEAVEN, CAVE
    }

    enum Weather {
        CLEAR, RAIN, SNOW, STORM, SANDSTORM
    }

    enum Difficulty {
        PEACEFUL("Мирная"), EASY("Лёгкая"), NORMAL("Нормальная"), HARD("Сложная");
        final String displayName;

        Difficulty(String n) {
            displayName = n;
        }
    }

    // ==================== ПОЛЯ ====================
    private GameState state = GameState.MENU;
    private GameMode mode = GameMode.SURVIVAL;
    private Difficulty difficulty = Difficulty.NORMAL;
    private Weather weather = Weather.CLEAR;
    private long weatherTimer = 0;

    private final javax.swing.Timer timer;
    private JFrame frame;

    private World world;
    private Player player;
    private WorldType currentWorldType = WorldType.NORMAL;

    private final List<Monster> monsters = new ArrayList<>();
    private final List<Animal> animals = new ArrayList<>();
    private final List<Villager> villagers = new ArrayList<>();
    private final List<FloatingText> floaters = new ArrayList<>();
    private final List<Arrow> arrows = new ArrayList<>();
    private final List<RemotePlayer> remotePlayers = new ArrayList<>();
    private final List<Achievement> achievements = new ArrayList<>();
    private final List<Dungeon> dungeons = new ArrayList<>();

    private final boolean[] keys = new boolean[256];
    private int mouseX, mouseY;
    private boolean mouseDown, rightMouseDown;

    private long gameTime = 0;
    private long lastFpsTime = System.currentTimeMillis();
    private int framesThisSecond = 0;
    private int fps = 0;

    private final List<WorldSave> worldSaves = new ArrayList<>();
    private int selectedWorldIndex = 0;
    private String currentWorldName = "world";
    private String inputSeed = "";
    private boolean typingSeed = false;

    private int newWorldWidth = 800;
    private int newWorldHeight = 200;
    private WorldType newWorldType = WorldType.NORMAL;
    private GameMode newWorldMode = GameMode.SURVIVAL;
    private Difficulty newWorldDifficulty = Difficulty.NORMAL;
    private double newWorldOreDensity = 1.0;
    private double newWorldTreeDensity = 1.0;
    private double newWorldMonsterRate = 1.0;
    private boolean newWorldStructures = true;
    private int worldSettingsTab = 0;

    private int settingsTab = 0;

    private final ItemStack[] inventory = new ItemStack[INV_COLS * INV_ROWS];
    private final ItemStack[] armorSlots = new ItemStack[ARMOR_SLOTS];
    private int selectedSlot = 0;
    private boolean inventoryOpen = false;
    private ItemStack draggedStack = null;
    private int draggedFromSlot = -1;

    private final ItemStack[] craftGrid = new ItemStack[CRAFT_SIZE];
    private ItemStack craftResult = null;
    private Crafting.Recipe currentRecipe = null;
    private boolean nearWorkbench = false;

    private WorkBlock activeContainer = null;
    private ItemStack[] containerSlots = null;

    private Villager tradingVillager = null;
    private int tradeScroll = 0;

    private int digX = -1, digY = -1;
    private int digProgress = 0;
    private int digRequired = 100;

    private MultiplayerManager mp = null;
    private boolean mpHost = false;
    private String mpAddress = "127.0.0.1";
    private boolean typingMpAddress = false;
    private String mpStatus = "";
    private List<String> mpPlayerList = new ArrayList<>();

    private boolean chatOpen = false;
    private String chatInput = "";
    private final List<ChatMessage> chatLog = new ArrayList<>();
    private int chatVisibleCount = 8;
    private int chatChannel = 0;

    private int xp = 0, xpLevel = 0, xpToNext = 20;

    private boolean fullscreen = false;
    private Rectangle windowedBounds;

    private static final List<ResourcePack> resourcePacks = new ArrayList<>();
    private int selectedPackIndex = 0;

    private float musicVolume = 0.55f;
    private float sfxVolume = 0.7f;
    private boolean showFPS = true;
    private boolean showCoordinates = false;
    private boolean autoSave = true;

    private String notifyText = "";
    private long notifyTime = 0;
    private Color notifyColor = Color.WHITE;

    private long uiAnimTime = 0;

    private int monsterSpawnCooldown = 0;
    private int animalSpawnCooldown = 0;

    // ==================== КОНСТРУКТОР ====================
    public TerraPixel(JFrame frame) {
        this.frame = frame;
        setPreferredSize(new Dimension(SCREEN_W, SCREEN_H));
        setBackground(Color.BLACK);
        setFocusable(true);
        setDoubleBuffered(true);
        addKeyListener(this);
        addMouseListener(this);
        addMouseMotionListener(this);
        addMouseWheelListener(this);

        try {
            frame.setIconImage(createMinecraftIcon());
        } catch (Exception ignored) {
        }

        ensureDirectories();
        refreshWorldSaves();
        initAchievements();
        refreshResourcePacks();
        loadSettings();

        Sound.init();
        Sound.setVolume(sfxVolume);
        Music.setVolume(musicVolume);

        timer = new javax.swing.Timer(16, this);
        timer.start();
    }

    // ==================== ИКОНКА MINECRAFT ====================
    private static BufferedImage createMinecraftIcon() {
        int S = 64;
        BufferedImage img = new BufferedImage(S, S, BufferedImage.TYPE_INT_ARGB);
        Graphics2D g = img.createGraphics();
        g.setRenderingHint(RenderingHints.KEY_INTERPOLATION,
                RenderingHints.VALUE_INTERPOLATION_NEAREST_NEIGHBOR);
        g.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
                RenderingHints.VALUE_ANTIALIAS_OFF);

        Random rnd = new Random(12345);

        // === ИЗОМЕТРИЧЕСКАЯ ИКОНКА БЛОКА ТРАВЫ ===
        // Рисуем три грани блока 3D-куба с наклоном
        // Размеры куба
        int cubeSize = 30;      // длина ребра
        int offsetX = 6;        // отступ
        int offsetY = 10;

        // Верхняя грань (ромб) — центр куба
        int[] topX = {
            offsetX + cubeSize / 2, // левый верх
            offsetX + cubeSize, // верх
            offsetX + cubeSize / 2 + cubeSize, // правый верх
            offsetX, // центр (нижний)
        };
        int[] topY = {
            offsetY, // верх
            offsetY + cubeSize / 3, // правый верх
            offsetY + cubeSize / 3 * 2, // правый низ
            offsetY + cubeSize / 3, // центр
        };

        // Рисуем верхнюю грань (трава — зелёная)
        for (int i = 0; i < cubeSize; i++) {
            for (int j = 0; j < cubeSize; j++) {
                int px = offsetX + (i - j) + cubeSize / 2;
                int py = offsetY + (i + j) / 3;
                if (px < 0 || py < 0 || px >= S || py >= S) {
                    continue;
                }

                int v = 60 + rnd.nextInt(40);
                int r = 40 + rnd.nextInt(20);
                int gr = 150 + v / 3;
                int b = 40 + rnd.nextInt(20);
                img.setRGB(px, py, new Color(r, gr, b).getRGB());
            }
        }

        // Левая грань (грязь — тёмная)
        for (int i = 0; i < cubeSize; i++) {
            for (int j = 0; j < cubeSize; j++) {
                int px = offsetX + i;
                int py = offsetY + cubeSize / 3 + j - i / 3;
                if (px < 0 || py < 0 || px >= S || py >= S) {
                    continue;
                }

                int v = 100 + rnd.nextInt(30);
                int r = 90 + rnd.nextInt(20);
                int gr = 60 + rnd.nextInt(15);
                int b = 35 + rnd.nextInt(10);
                img.setRGB(px, py, new Color(r, gr, b).getRGB());
            }
        }

        // Правая грань (грязь — светлая)
        for (int i = 0; i < cubeSize; i++) {
            for (int j = 0; j < cubeSize; j++) {
                int px = offsetX + cubeSize / 2 + i;
                int py = offsetY + cubeSize / 3 * 2 + j - i / 3;
                if (px < 0 || py < 0 || px >= S || py >= S) {
                    continue;
                }

                int v = 120 + rnd.nextInt(30);
                int r = 110 + rnd.nextInt(20);
                int gr = 75 + rnd.nextInt(15);
                int b = 45 + rnd.nextInt(10);
                img.setRGB(px, py, new Color(r, gr, b).getRGB());
            }
        }

        // Обводка блока (тёмная)
        g.setColor(new Color(30, 20, 10, 220));
        // Верх
        g.drawLine(offsetX + cubeSize / 2, offsetY, offsetX + cubeSize, offsetY + cubeSize / 3);
        g.drawLine(offsetX + cubeSize, offsetY + cubeSize / 3,
                offsetX + cubeSize / 2 + cubeSize, offsetY + cubeSize / 3 * 2);
        g.drawLine(offsetX + cubeSize / 2 + cubeSize, offsetY + cubeSize / 3 * 2,
                offsetX, offsetY + cubeSize / 3);
        g.drawLine(offsetX, offsetY + cubeSize / 3,
                offsetX + cubeSize / 2, offsetY);
        // Вертикали
        g.drawLine(offsetX, offsetY + cubeSize / 3, offsetX, offsetY + cubeSize / 3 + cubeSize);
        g.drawLine(offsetX + cubeSize / 2, offsetY, offsetX + cubeSize / 2, offsetY + cubeSize);
        g.drawLine(offsetX + cubeSize / 2 + cubeSize, offsetY + cubeSize / 3 * 2,
                offsetX + cubeSize / 2 + cubeSize, offsetY + cubeSize / 3 * 2 + cubeSize);
        // Низ
        g.drawLine(offsetX, offsetY + cubeSize / 3 + cubeSize,
                offsetX + cubeSize / 2, offsetY + cubeSize);
        g.drawLine(offsetX + cubeSize / 2, offsetY + cubeSize,
                offsetX + cubeSize / 2 + cubeSize, offsetY + cubeSize / 3 * 2 + cubeSize);
        g.drawLine(offsetX + cubeSize / 2 + cubeSize, offsetY + cubeSize / 3 * 2 + cubeSize,
                offsetX + cubeSize / 2, offsetY + cubeSize * 2 / 3 + cubeSize / 3);

        // Блики (светлые)
        g.setColor(new Color(255, 255, 255, 60));
        for (int i = 0; i < 10; i++) {
            int x = rnd.nextInt(cubeSize);
            int y = rnd.nextInt(cubeSize);
            g.fillRect(offsetX + x + 4, offsetY + y, 1, 1);
        }

        // Тени (тёмные)
        g.setColor(new Color(0, 0, 0, 100));
        for (int i = 0; i < 8; i++) {
            int x = rnd.nextInt(cubeSize);
            int y = rnd.nextInt(cubeSize);
            g.fillRect(offsetX + x, offsetY + cubeSize / 3 + y, 1, 1);
        }

        g.dispose();
        return img;
    }

    private void ensureDirectories() {
        new File("saves").mkdirs();
        new File("config").mkdirs();
        new File("resourcepacks").mkdirs();
    }

    private void initAchievements() {
        achievements.add(new Achievement("first_block", "Первый блок", "Сломай первый блок", "blocks"));
        achievements.add(new Achievement("wood", "Лесоруб", "Собери 10 дерева", "blocks"));
        achievements.add(new Achievement("iron", "Железный человек", "Получи железный слиток", "items"));
        achievements.add(new Achievement("gold", "Золотая жила", "Найди золото", "items"));
        achievements.add(new Achievement("diamond", "Алмазный добытчик", "Найди алмаз", "items"));
        achievements.add(new Achievement("first_monster", "Охотник", "Убей первого монстра", "mobs"));
        achievements.add(new Achievement("village", "Путешественник", "Найди деревню", "world"));
        achievements.add(new Achievement("night", "Ночной страж", "Переживи первую ночь", "world"));
        achievements.add(new Achievement("smelt", "Плавка", "Переплавь руду в печи", "items"));
        achievements.add(new Achievement("rich", "Богач", "Накопи 100 золотых монет", "items"));
        achievements.add(new Achievement("level5", "Опытный", "Достигни 5 уровня", "player"));
        achievements.add(new Achievement("craft", "Ремесленник", "Скрафти первый предмет", "items"));
        achievements.add(new Achievement("multiplayer", "Сетевой игрок", "Подключись к серверу", "mp"));
        achievements.add(new Achievement("armor", "Бронированный", "Надень полный комплект брони", "player"));
        achievements.add(new Achievement("trade", "Торговец", "Соверши первую сделку", "village"));
        achievements.add(new Achievement("animal", "Фермер", "Убей или приручи животное", "mobs"));
        achievements.add(new Achievement("dungeon", "Искатель приключений", "Найди подземелье", "world"));
        achievements.add(new Achievement("stick", "Палка", "Скрафти первую палку", "items"));
        achievements.add(new Achievement("torch", "Свет", "Скрафти факел", "items"));
    }

    private void refreshWorldSaves() {
        worldSaves.clear();
        File dir = new File("saves");
        File[] files = dir.listFiles((d, n) -> n.endsWith(".world"));
        if (files != null) {
            for (File f : files) {
                try {
                    WorldSave ws = new WorldSave();
                    ws.file = f;
                    ws.name = f.getName().replace(".world", "");
                    ws.size = f.length();
                    long lastMod = f.lastModified();
                    java.text.SimpleDateFormat sdf = new java.text.SimpleDateFormat("dd.MM.yyyy HH:mm");
                    ws.dateStr = sdf.format(new Date(lastMod));
                    try (ObjectInputStream in = new ObjectInputStream(new FileInputStream(f))) {
                        Object obj = in.readObject();
                        if (obj instanceof World) {
                            World w = (World) obj;
                            ws.sizeW = w.getWidth();
                            ws.sizeH = w.getHeight();
                            ws.worldType = w.worldType;
                            ws.mode = w.mode;
                            ws.iconSeed = w.seed;
                        }
                    } catch (Exception e) {
                        ws.sizeW = 0;
                        ws.sizeH = 0;
                    }
                    worldSaves.add(ws);
                } catch (Exception ignored) {
                }
            }
        }
        worldSaves.sort((a, b) -> Long.compare(b.file.lastModified(), a.file.lastModified()));
    }

    private void refreshResourcePacks() {
        for (ResourcePack rp : resourcePacks) {
            rp.close();
        }
        resourcePacks.clear();

        ResourcePack def = new ResourcePack();
        def.name = "default";
        def.description = "Встроенные текстуры TerraPixel (Faithful)";
        def.author = "TerraPixel Team";
        def.version = "1.0";
        def.active = true;
        def.isDefault = true;
        resourcePacks.add(def);

        List<File> searchDirs = new ArrayList<>();
        searchDirs.add(new File("resourcepacks"));
        searchDirs.add(new File("resources/resourcepacks"));

        String appData = System.getenv("APPDATA");
        if (appData != null) {
            searchDirs.add(new File(appData + "/.terrapixel/resourcepacks"));
        }
        String home = System.getProperty("user.home");
        if (home != null) {
            searchDirs.add(new File(home + "/.terrapixel/resourcepacks"));
        }

        Set<String> seen = new HashSet<>();
        for (File dir : searchDirs) {
            if (!dir.exists()) {
                continue;
            }
            File[] items = dir.listFiles();
            if (items == null) {
                continue;
            }
            for (File item : items) {
                String key = item.getName().toLowerCase();
                if (seen.contains(key)) {
                    continue;
                }
                seen.add(key);

                if (item.isDirectory()) {
                    ResourcePack rp = loadPackFromFolder(item);
                    if (rp != null) {
                        resourcePacks.add(rp);
                    }
                } else if (item.getName().endsWith(".zip")) {
                    ResourcePack rp = loadPackFromZip(item);
                    if (rp != null) {
                        resourcePacks.add(rp);
                    }
                }
            }
        }
    }

    private ResourcePack loadPackFromFolder(File folder) {
        try {
            ResourcePack rp = new ResourcePack();
            rp.folder = folder;
            rp.name = folder.getName();
            rp.isZip = false;
            File pj = new File(folder, "pack.json");
            if (pj.exists()) {
                String json = new String(java.nio.file.Files.readAllBytes(pj.toPath()));
                rp.description = parseJsonField(json, "description");
                rp.author = parseJsonField(json, "author");
                rp.version = parseJsonField(json, "version");
                String name = parseJsonField(json, "name");
                if (!name.isEmpty()) {
                    rp.name = name;
                }
            }
            return rp;
        } catch (Exception e) {
            return null;
        }
    }

    private ResourcePack loadPackFromZip(File zip) {
        try {
            ResourcePack rp = new ResourcePack();
            rp.folder = zip;
            rp.isZip = true;
            rp.zipFile = new ZipFile(zip);
            rp.name = zip.getName().replace(".zip", "");
            ZipEntry entry = rp.zipFile.getEntry("pack.json");
            if (entry != null) {
                try (InputStream is = rp.zipFile.getInputStream(entry)) {
                    String json = new String(is.readAllBytes());
                    rp.description = parseJsonField(json, "description");
                    rp.author = parseJsonField(json, "author");
                    rp.version = parseJsonField(json, "version");
                    String name = parseJsonField(json, "name");
                    if (!name.isEmpty()) {
                        rp.name = name;
                    }
                }
            }
            return rp;
        } catch (Exception e) {
            return null;
        }
    }

    private String parseJsonField(String json, String field) {
        try {
            int idx = json.indexOf("\"" + field + "\"");
            if (idx < 0) {
                return "";
            }
            int start = json.indexOf('"', idx + field.length() + 2) + 1;
            int end = json.indexOf('"', start);
            return json.substring(start, end);
        } catch (Exception e) {
            return "";
        }
    }

    private void loadSettings() {
        File f = new File("config/settings.json");
        if (!f.exists()) {
            return;
        }
        try {
            String content = new String(java.nio.file.Files.readAllBytes(f.toPath()));
            musicVolume = (float) parseDouble(content, "musicVolume", 0.55);
            sfxVolume = (float) parseDouble(content, "sfxVolume", 0.7);
            showFPS = parseBool(content, "showFPS", true);
            showCoordinates = parseBool(content, "showCoordinates", false);
            autoSave = parseBool(content, "autoSave", true);
        } catch (Exception ignored) {
        }
    }

    private void saveSettings() {
        try (PrintWriter pw = new PrintWriter("config/settings.json")) {
            pw.println("{");
            pw.println("  \"musicVolume\": " + musicVolume + ",");
            pw.println("  \"sfxVolume\": " + sfxVolume + ",");
            pw.println("  \"showFPS\": " + showFPS + ",");
            pw.println("  \"showCoordinates\": " + showCoordinates + ",");
            pw.println("  \"autoSave\": " + autoSave);
            pw.println("}");
        } catch (Exception ignored) {
        }
    }

    private double parseDouble(String json, String field, double def) {
        try {
            int idx = json.indexOf("\"" + field + "\"");
            if (idx < 0) {
                return def;
            }
            int colon = json.indexOf(':', idx);
            int end = json.indexOf(',', colon);
            if (end < 0) {
                end = json.indexOf('}', colon);
            }
            return Double.parseDouble(json.substring(colon + 1, end).trim());
        } catch (Exception e) {
            return def;
        }
    }

    private boolean parseBool(String json, String field, boolean def) {
        try {
            int idx = json.indexOf("\"" + field + "\"");
            if (idx < 0) {
                return def;
            }
            int colon = json.indexOf(':', idx);
            int end = json.indexOf(',', colon);
            if (end < 0) {
                end = json.indexOf('}', colon);
            }
            return Boolean.parseBoolean(json.substring(colon + 1, end).trim());
        } catch (Exception e) {
            return def;
        }
    }

    private void notify(String text, Color color) {
        notifyText = text;
        notifyColor = color;
        notifyTime = System.currentTimeMillis();
    }

    private void addChatMessage(String text, Color color) {
        chatLog.add(new ChatMessage(text, color, System.currentTimeMillis()));
        if (chatLog.size() > 100) {
            chatLog.remove(0);
        }
    }
    // ==================== ОСНОВНОЙ ЦИКЛ ====================

    @Override
    public void actionPerformed(ActionEvent e) {
        uiAnimTime++;
        framesThisSecond++;
        long now = System.currentTimeMillis();
        if (now - lastFpsTime >= 1000) {
            fps = framesThisSecond;
            framesThisSecond = 0;
            lastFpsTime = now;
        }

        if (state == GameState.MENU || state == GameState.WORLD_SELECT) {
            Music.playMenuMusic();
        } else if (state == GameState.PLAYING) {
            Music.playGameMusic();
        } else {
            Music.stop();
        }

        if (state == GameState.PLAYING) {
            gameTime++;
            updatePlaying();
        } else if (state == GameState.MP_HOST_WAITING) {
            if (mp != null) {
                mp.tickHostWaiting();
            }
        }

        if (state == GameState.PLAYING) {
            weatherTimer++;
            if (weatherTimer > 60 * 60 * 5) {
                weatherTimer = 0;
                changeWeather();
            }
        }

        repaint();
    }

    private void changeWeather() {
        Random rnd = new Random();
        int r = rnd.nextInt(100);
        if (r < 60) {
            weather = Weather.CLEAR;
        } else if (r < 80) {
            weather = Weather.RAIN;
        } else if (r < 90) {
            weather = Weather.SNOW;
        } else if (r < 97) {
            weather = Weather.STORM;
        } else {
            weather = Weather.SANDSTORM;
        }

        if (weather != Weather.CLEAR) {
            String wname = "";
            switch (weather) {
                case RAIN:
                    wname = "Дождь";
                    break;
                case SNOW:
                    wname = "Снег";
                    break;
                case STORM:
                    wname = "Гроза";
                    break;
                case SANDSTORM:
                    wname = "Песчаная буря";
                    break;
            }
            notify("Погода: " + wname, new Color(150, 200, 255));
        }
    }

    private void updatePlaying() {
        if (player == null || world == null) {
            return;
        }
        if (world.getWidth() <= 10) {
            return;
        }

        if (mp != null) {
            mp.tick(player);
            mp.updateRemotePlayers(remotePlayers);
        }

        nearWorkbench = false;
        int pxTile = (int) (player.x / TILE);
        int pyTile = (int) (player.y / TILE);
        for (int dx = -3; dx <= 3; dx++) {
            for (int dy = -3; dy <= 3; dy++) {
                int b = world.getBlock(pxTile + dx, pyTile + dy);
                if (b == World.WORKBENCH || b == World.CRAFT_TABLE) {
                    nearWorkbench = true;
                    break;
                }
            }
            if (nearWorkbench) {
                break;
            }
        }

        if (!chatOpen && !inventoryOpen) {
            double dx = 0;
            if (keys[KeyEvent.VK_A] || keys[KeyEvent.VK_LEFT]) {
                dx -= 1;
            }
            if (keys[KeyEvent.VK_D] || keys[KeyEvent.VK_RIGHT]) {
                dx += 1;
            }
            boolean jump = keys[KeyEvent.VK_SPACE] || keys[KeyEvent.VK_W] || keys[KeyEvent.VK_UP];
            player.update(dx, jump, world);
            checkFallDamage();
        }

        world.tick();

        for (WorkBlock wb : world.workBlocks) {
            if (wb.type == World.FURNACE) {
                int before = wb.getResultCount();
                wb.tickFurnace();
                if (wb.getResultCount() > before) {
                    unlock("smelt");
                }
            }
        }

        for (Iterator<Monster> it = monsters.iterator(); it.hasNext();) {
            Monster m = it.next();
            m.update(player, world, monsters);
            if (m.dead) {
                it.remove();
            }
        }

        for (Iterator<Animal> it = animals.iterator(); it.hasNext();) {
            Animal a = it.next();
            a.update(world, player);
            if (a.dead) {
                it.remove();
            }
        }

        for (Iterator<Arrow> it = arrows.iterator(); it.hasNext();) {
            Arrow ar = it.next();
            ar.update(world, monsters);
            if (ar.dead) {
                it.remove();
            }
        }

        for (Villager v : villagers) {
            v.update(world);
        }

        if (isNight() && difficulty != Difficulty.PEACEFUL) {
            monsterSpawnCooldown--;
            if (monsterSpawnCooldown <= 0 && monsters.size() < 20 * newWorldMonsterRate) {
                spawnMonsterNearPlayer();
                monsterSpawnCooldown = 60 + new Random().nextInt(120);
            }
            if (gameTime > DAY_LENGTH / 2) {
                unlock("night");
            }
        } else {
            for (Monster m : monsters) {
                int bx = (int) (m.x / TILE);
                int by = (int) (m.y / TILE);
                if (world.getBlock(bx, by) == World.AIR && world.getBlock(bx, by - 1) == World.AIR) {
                    m.hp -= 0.5;
                    if (m.hp <= 0) {
                        m.dead = true;
                    }
                }
            }
        }

        if (!isNight() && animals.size() < 15) {
            animalSpawnCooldown--;
            if (animalSpawnCooldown <= 0) {
                spawnAnimalNearPlayer();
                animalSpawnCooldown = 200 + new Random().nextInt(300);
            }
        }

        for (Iterator<FloatingText> it = floaters.iterator(); it.hasNext();) {
            FloatingText ft = it.next();
            ft.y -= 0.5;
            ft.life--;
            if (ft.life <= 0) {
                it.remove();
            }
        }

        if (mouseDown && !inventoryOpen && digX >= 0) {
            continueDigging();
        } else {
            digProgress = 0;
            digX = -1;
        }

        if (player.hp <= 0 && state == GameState.PLAYING) {
            state = GameState.DEAD;
            Sound.play(Sound.DEATH);
            addChatMessage("Ты умер!", new Color(255, 100, 100));
            if (mode == GameMode.SURVIVAL) {
                for (int i = 0; i < inventory.length; i++) {
                    inventory[i] = null;
                }
                for (int i = 0; i < armorSlots.length; i++) {
                    armorSlots[i] = null;
                }
            }
        }

        if (Modules.HUNGER_SYSTEM && difficulty != Difficulty.PEACEFUL) {
            if (player.hunger < 20 && !isNight() && player.hunger > 0) {
                int bx = (int) (player.x / TILE);
                int by = (int) (player.y / TILE);
                if (world.getBlock(bx, by + 1) == World.GRASS) {
                    player.hunger += 0.02;
                    if (player.hunger > player.maxHunger) {
                        player.hunger = player.maxHunger;
                    }
                }
            }
        }
    }

    private void checkFallDamage() {
        if (!Modules.FALL_DAMAGE) {
            return;
        }
        if (player == null) {
            return;
        }
        if (difficulty == Difficulty.PEACEFUL) {
            return;
        }

        if (!player.onGround) {
            if (!player.wasInAir) {
                player.fallStartY = player.y;
                player.wasInAir = true;
            }
            return;
        }
        if (player.wasInAir) {
            double fallDist = (player.fallStartY - player.y) / TILE;
            if (fallDist > 4.0) {
                int dmg = (int) ((fallDist - 4.0) * 8);
                if (difficulty == Difficulty.EASY) {
                    dmg = (int) (dmg * 0.5);
                } else if (difficulty == Difficulty.HARD) {
                    dmg = (int) (dmg * 1.5);
                }
                if (dmg > 0 && !player.godMode) {
                    player.hp -= dmg;
                    player.hurtCooldown = 30;
                    floaters.add(new FloatingText("-" + dmg + " HP", player.x, player.y - 20,
                            new Color(255, 80, 80)));
                    Sound.play(Sound.HURT);
                }
            }
            player.wasInAir = false;
        }
    }

    private boolean isNight() {
        return (gameTime % DAY_LENGTH) / (double) DAY_LENGTH > 0.5;
    }

    private double dayProgress() {
        return (gameTime % DAY_LENGTH) / (double) DAY_LENGTH;
    }

    private void spawnMonsterNearPlayer() {
        Random rnd = new Random();
        int side = rnd.nextBoolean() ? 1 : -1;
        int dist = 15 + rnd.nextInt(10);
        double mx = player.x + side * dist * TILE;
        double my = player.y - rnd.nextInt(3) * TILE;
        int tx = (int) (mx / TILE);
        int ty = (int) (my / TILE);
        for (int i = 0; i < 20; i++) {
            if (ty + i < world.getHeight() && world.isSolid(tx, ty + i)) {
                my = (ty + i) * TILE - Monster.H;
                break;
            }
        }
        if (tx < 2 || tx > world.getWidth() - 2) {
            return;
        }
        int type = rnd.nextInt(5);
        monsters.add(new Monster(mx, my, type));
    }

    private void spawnAnimalNearPlayer() {
        Random rnd = new Random();
        int side = rnd.nextBoolean() ? 1 : -1;
        int dist = 10 + rnd.nextInt(15);
        double mx = player.x + side * dist * TILE;
        double my = player.y - rnd.nextInt(3) * TILE;
        int tx = (int) (mx / TILE);
        int ty = (int) (my / TILE);
        for (int i = 0; i < 20; i++) {
            if (ty + i < world.getHeight() && world.isSolid(tx, ty + i)) {
                my = (ty + i) * TILE - Animal.H;
                break;
            }
        }
        if (tx < 2 || tx > world.getWidth() - 2) {
            return;
        }
        int type = rnd.nextInt(4);
        animals.add(new Animal(mx, my, type));
    }

    private void addToInventory(ItemStack stack) {
        if (stack == null) {
            return;
        }
        for (int i = 0; i < inventory.length; i++) {
            if (inventory[i] != null && inventory[i].id == stack.id && inventory[i].count < 999) {
                inventory[i].count += stack.count;
                if (inventory[i].count > 999) {
                    inventory[i].count = 999;
                }
                return;
            }
        }
        for (int i = 0; i < inventory.length; i++) {
            if (inventory[i] == null) {
                inventory[i] = stack.copy();
                return;
            }
        }
    }

    private void addXp(int amount) {
        xp += amount;
        while (xp >= xpToNext) {
            xp -= xpToNext;
            xpLevel++;
            xpToNext = 20 + xpLevel * 10;
            Sound.play(Sound.ACHIEVEMENT);
            notify("Уровень " + xpLevel + "!", new Color(200, 140, 255));
            if (xpLevel >= 5) {
                unlock("level5");
            }
        }
    }

    private int countItem(int id) {
        int n = 0;
        for (ItemStack s : inventory) {
            if (s != null && s.id == id) {
                n += s.count;
            }
        }
        return n;
    }

    private void removeItem(int id, int count) {
        for (int i = 0; i < inventory.length && count > 0; i++) {
            if (inventory[i] != null && inventory[i].id == id) {
                int take = Math.min(count, inventory[i].count);
                inventory[i].count -= take;
                count -= take;
                if (inventory[i].count <= 0) {
                    inventory[i] = null;
                }
            }
        }
    }

    private void unlock(String id) {
        for (Achievement a : achievements) {
            if (a.id.equals(id) && !a.unlocked) {
                a.unlocked = true;
                if (player != null) {
                    floaters.add(new FloatingText("★ " + a.title, player.x, player.y - 50,
                            new Color(255, 220, 100)));
                }
                notify("★ " + a.title, new Color(255, 220, 100));
                Sound.play(Sound.ACHIEVEMENT);
            }
        }
    }

    // ==================== РЕНДЕР ====================
    @Override
    protected void paintComponent(Graphics g) {
        super.paintComponent(g);
        Graphics2D g2 = (Graphics2D) g;
        g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_OFF);
        g2.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING, RenderingHints.VALUE_TEXT_ANTIALIAS_OFF);
        g2.setRenderingHint(RenderingHints.KEY_INTERPOLATION, RenderingHints.VALUE_INTERPOLATION_NEAREST_NEIGHBOR);

        switch (state) {
            case MENU:
                drawMenu(g2);
                break;
            case WORLD_SELECT:
                drawWorldSelect(g2);
                break;
            case WORLD_CREATE:
                drawWorldCreate(g2);
                break;
            case PLAYING:
                drawGame(g2);
                break;
            case PAUSED:
                drawGame(g2);
                drawPause(g2);
                break;
            case DEAD:
                drawGame(g2);
                drawDeath(g2);
                break;
            case ACHIEVEMENTS:
                drawAchievements(g2);
                break;
            case SETTINGS:
                drawSettings(g2);
                break;
            case MULTIPLAYER:
                drawMultiplayer(g2);
                break;
            case MP_HOST_WAITING:
                drawMpHostWaiting(g2);
                break;
            case LOADING:
                drawLoading(g2);
                break;
            case RESOURCEPACKS:
                drawResourcePacks(g2);
                break;
            case TRADE:
                drawGame(g2);
                drawTrade(g2);
                break;
        }

        drawNotification(g2);
    }

    private void drawMenu(Graphics2D g) {
        g.setColor(new Color(16, 16, 24));
        g.fillRect(0, 0, SCREEN_W, SCREEN_H);

        GradientPaint glow = new GradientPaint(0, 0, new Color(60, 80, 140, 90),
                0, SCREEN_H / 2, new Color(0, 0, 0, 0));
        g.setPaint(glow);
        g.fillRect(0, 0, SCREEN_W, SCREEN_H / 2);

        drawMenuBackground(g);

        g.setColor(new Color(0, 0, 0, 130));
        g.fillRect(0, 0, SCREEN_W, SCREEN_H);

        g.setFont(PixelFont.font(72, Font.BOLD));
        drawCenteredWithPixelShadow(g, "TerraPixel", SCREEN_W / 2, 130,
                new Color(255, 220, 80));

        long t = System.currentTimeMillis();
        double pulse = 1.0 + Math.sin(t / 200.0) * 0.08;
        Graphics2D g2 = (Graphics2D) g.create();
        g2.translate(SCREEN_W / 2 + 160, 115);
        g2.rotate(-0.3);
        g2.scale(pulse, pulse);
        g2.setFont(PixelFont.font(14, Font.BOLD));
        g2.setColor(new Color(0, 0, 0, 220));
        g2.drawString("Faithful Edition!", 2, 2);
        g2.setColor(new Color(255, 255, 80));
        g2.drawString("Faithful Edition!", 0, 0);
        g2.dispose();

        g.setFont(PixelFont.font(11, Font.BOLD));
        g.setColor(new Color(140, 140, 160));
        String verStr = "TerraPixel " + VERSION;
        FontMetrics fmV = g.getFontMetrics();
        g.drawString(verStr, SCREEN_W - fmV.stringWidth(verStr) - 8, 20);

        String[] items = {"Одиночная игра", "Мультиплеер", "Настройки", "Выход"};
        int startY = 240;
        for (int i = 0; i < items.length; i++) {
            int y = startY + i * 55;
            int bx = SCREEN_W / 2 - 200;
            int bw = 400, bh = 42;
            boolean hover = mouseY > y && mouseY < y + bh
                    && mouseX > bx && mouseX < bx + bw;
            drawMCButton(g, items[i], bx, y, bw, bh, hover);
        }

        g.setFont(PixelFont.font(11, Font.PLAIN));
        g.setColor(new Color(180, 180, 180));
        drawCentered(g, "Copyright Mojang AB. Do not distribute!",
                SCREEN_W / 2, SCREEN_H - 12);

        g.setColor(new Color(120, 140, 160));
        g.drawString("FPS: " + fps, 6, 16);
    }

    private void drawMenuBackground(Graphics2D g) {
        Random rnd = new Random(1337);
        g.setColor(new Color(40, 60, 100));
        g.fillRect(0, 0, SCREEN_W, SCREEN_H / 2);
        for (int i = 0; i < 12; i++) {
            int cx = rnd.nextInt(SCREEN_W);
            int cy = 20 + rnd.nextInt(SCREEN_H / 3);
            int cw = 80 + rnd.nextInt(160);
            int ch = 20 + rnd.nextInt(20);
            g.setColor(new Color(255, 255, 255, 30 + rnd.nextInt(30)));
            g.fillRect(cx, cy, cw, ch);
        }
        for (int i = 0; i < 6; i++) {
            int mx = rnd.nextInt(SCREEN_W);
            int mh = 100 + rnd.nextInt(150);
            g.setColor(new Color(30 + rnd.nextInt(20), 40 + rnd.nextInt(30), 30 + rnd.nextInt(20)));
            int[] xs = {mx - 200, mx, mx + 200};
            int[] ys = {SCREEN_H, SCREEN_H - mh, SCREEN_H};
            g.fillPolygon(xs, ys, 3);
        }
    }

    private void drawMCButton(Graphics2D g, String text, int x, int y, int w, int h,
            boolean hover) {
        g.setColor(new Color(0, 0, 0, 200));
        g.fillRect(x - 2, y - 2, w + 4, h + 4);

        Color top = hover ? new Color(140, 140, 140) : new Color(80, 80, 80);
        Color bot = hover ? new Color(100, 100, 100) : new Color(60, 60, 60);
        for (int i = 0; i < h; i++) {
            float f = i / (float) h;
            int r = (int) (top.getRed() * (1 - f) + bot.getRed() * f);
            int gr = (int) (top.getGreen() * (1 - f) + bot.getGreen() * f);
            int b = (int) (top.getBlue() * (1 - f) + bot.getBlue() * f);
            g.setColor(new Color(r, gr, b));
            g.fillRect(x, y + i, w, 1);
        }

        g.setColor(new Color(255, 255, 255, hover ? 120 : 60));
        g.drawLine(x + 1, y + 1, x + w - 2, y + 1);
        g.setColor(new Color(0, 0, 0, 150));
        g.drawLine(x + 1, y + h - 2, x + w - 2, y + h - 2);

        g.setColor(hover ? Color.WHITE : new Color(160, 160, 160));
        g.drawRect(x, y, w - 1, h - 1);

        g.setFont(PixelFont.font(20, Font.BOLD));
        FontMetrics fm = g.getFontMetrics();
        int tx = x + (w - fm.stringWidth(text)) / 2;
        int ty = y + (h + fm.getAscent()) / 2 - 5;
        g.setColor(new Color(0, 0, 0, 220));
        g.drawString(text, tx + 2, ty + 2);
        g.setColor(hover ? new Color(255, 255, 100) : Color.WHITE);
        g.drawString(text, tx, ty);
    }

    private void drawPixelButton(Graphics2D g, String text, int x, int y, int w, int h, boolean hover) {
        drawMCButton(g, text, x, y, w, h, hover);
    }

    private void drawPixelButtonWithIcon(Graphics2D g, String text, int x, int y, int w, int h,
            boolean hover, BufferedImage icon) {
        drawMCButton(g, text, x, y, w, h, hover);
        if (icon != null) {
            g.drawImage(icon, x + 10, y + (h - 32) / 2, 32, 32, null);
        }
    }

    private void drawPixelPanel(Graphics2D g, int x, int y, int w, int h) {
        g.setColor(new Color(0, 0, 0, 220));
        g.fillRect(x - 4, y - 4, w + 8, h + 8);
        g.setColor(new Color(140, 110, 80));
        g.fillRect(x - 3, y - 3, w + 6, h + 6);
        g.setColor(new Color(90, 65, 40));
        g.fillRect(x - 1, y - 1, w + 2, h + 2);
        g.setColor(new Color(45, 33, 20));
        g.fillRect(x, y, w, h);
    }

    private void drawMinecraftSlot(Graphics2D g, int sx, int sy, boolean selected) {
        g.setColor(new Color(139, 139, 139));
        g.fillRect(sx, sy, SLOT - 2, SLOT - 2);
        g.setColor(new Color(55, 55, 55));
        g.fillRect(sx + 2, sy + 2, SLOT - 6, SLOT - 6);
        g.setColor(new Color(0, 0, 0, 100));
        g.drawRect(sx, sy, SLOT - 2, SLOT - 2);
        g.setColor(new Color(255, 255, 255, 180));
        g.drawLine(sx + 2, sy + 2, sx + SLOT - 4, sy + 2);
        g.drawLine(sx + 2, sy + 2, sx + 2, sy + SLOT - 4);
        if (selected) {
            g.setColor(new Color(255, 255, 255));
            g.drawRect(sx - 2, sy - 2, SLOT + 2, SLOT + 2);
            g.drawRect(sx - 3, sy - 3, SLOT + 4, SLOT + 4);
        }
    }

    private void drawCentered(Graphics2D g, String s, int cx, int y) {
        FontMetrics fm = g.getFontMetrics();
        g.drawString(s, cx - fm.stringWidth(s) / 2, y);
    }

    private void drawCenteredWithPixelShadow(Graphics2D g, String s, int cx, int y, Color color) {
        FontMetrics fm = g.getFontMetrics();
        int x = cx - fm.stringWidth(s) / 2;
        g.setColor(new Color(0, 0, 0, 220));
        g.drawString(s, x + 4, y + 4);
        g.setColor(color);
        g.drawString(s, x, y);
    }

    private void drawNotification(Graphics2D g) {
        if (System.currentTimeMillis() - notifyTime > 3000) {
            return;
        }
        if (notifyText == null || notifyText.isEmpty()) {
            return;
        }
        long elapsed = System.currentTimeMillis() - notifyTime;
        float alpha = elapsed > 2500 ? (3000 - elapsed) / 500f : 1f;
        int alphaInt = (int) (alpha * 255);

        g.setFont(PixelFont.font(18, Font.BOLD));
        FontMetrics fm = g.getFontMetrics();
        int tw = fm.stringWidth(notifyText);
        int x = SCREEN_W - tw - 40;
        int y = 20;

        g.setColor(new Color(0, 0, 0, (int) (200 * alpha)));
        g.fillRect(x - 10, y - 5, tw + 20, 30);
        g.setColor(new Color(notifyColor.getRed(), notifyColor.getGreen(),
                notifyColor.getBlue(), alphaInt));
        g.drawRect(x - 10, y - 5, tw + 20, 30);
        g.drawString(notifyText, x, y + 18);
    }

    // ==================== ВЫБОР МИРА ====================
    private void drawWorldSelect(Graphics2D g) {
        drawMenuBackground(g);
        g.setColor(new Color(0, 0, 0, 160));
        g.fillRect(0, 0, SCREEN_W, SCREEN_H);

        g.setFont(PixelFont.font(42, Font.BOLD));
        drawCenteredWithPixelShadow(g, "Выбор мира", SCREEN_W / 2, 55, new Color(255, 220, 80));

        int listX = 60, listY = 110, itemH = 70, listW = 520;
        if (worldSaves.isEmpty()) {
            g.setColor(new Color(200, 200, 220));
            g.setFont(PixelFont.font(18, Font.PLAIN));
            g.drawString("Пока нет миров. Создай новый!", listX + 20, listY + 40);
        }
        for (int i = 0; i < Math.min(worldSaves.size(), 6); i++) {
            int y = listY + i * itemH;
            WorldSave ws = worldSaves.get(i);
            boolean sel = i == selectedWorldIndex;
            boolean hover = mouseY > y && mouseY < y + itemH - 6 && mouseX > listX && mouseX < listX + listW;

            g.setColor(sel ? new Color(120, 90, 40, 230) : (hover ? new Color(70, 60, 50, 220) : new Color(40, 35, 30, 220)));
            g.fillRect(listX, y, listW, itemH - 6);
            g.setColor(sel ? new Color(255, 220, 100) : new Color(120, 90, 60));
            g.drawRect(listX, y, listW, itemH - 6);

            int iconSize = itemH - 20;
            drawWorldIcon(g, listX + 10, y + 10, iconSize, ws);

            g.setColor(sel ? new Color(255, 255, 200) : Color.WHITE);
            g.setFont(PixelFont.font(18, Font.BOLD));
            g.drawString((sel ? "> " : "  ") + ws.name, listX + iconSize + 25, y + 25);

            g.setColor(new Color(180, 180, 200));
            g.setFont(PixelFont.font(11, Font.PLAIN));
            String typeStr = ws.worldType != null ? ws.worldType.displayName : "Обычный";
            g.drawString("Тип: " + typeStr + "  ·  " + ws.sizeW + "×" + ws.sizeH, listX + iconSize + 30, y + 45);
            g.drawString("Дата: " + ws.dateStr, listX + iconSize + 30, y + 60);
        }

        drawMCButton(g, "Создать [N]", 60, 540, 250, 50,
                mouseY > 540 && mouseY < 590 && mouseX > 60 && mouseX < 310);
        drawMCButton(g, "Назад [Esc]", 60, 600, 200, 50,
                mouseY > 600 && mouseY < 650 && mouseX > 60 && mouseX < 260);
        if (!worldSaves.isEmpty()) {
            drawMCButton(g, "Играть [Enter]", 330, 540, 250, 50,
                    mouseY > 540 && mouseY < 590 && mouseX > 330 && mouseX < 580);
            drawMCButton(g, "Удалить [Del]", 330, 600, 250, 50,
                    mouseY > 600 && mouseY < 650 && mouseX > 330 && mouseX < 580);
        }
    }

    private void drawWorldIcon(Graphics2D g, int x, int y, int size, WorldSave ws) {
        g.setColor(new Color(30, 40, 70));
        g.fillRect(x, y, size, size);
        Random rnd = new Random(ws.iconSeed);
        g.setColor(new Color(100, 170, 240));
        g.fillRect(x, y, size, size / 2);
        int groundY = y + size / 2 + rnd.nextInt(3) - 1;
        g.setColor(new Color(70, 160, 70));
        g.fillRect(x, groundY, size, size - (groundY - y));
        for (int i = 0; i < 8; i++) {
            int bx = x + rnd.nextInt(size);
            int by = groundY + rnd.nextInt(size - (groundY - y));
            g.setColor(new Color(80 + rnd.nextInt(40), 80 + rnd.nextInt(40), 90 + rnd.nextInt(40)));
            g.fillRect(bx, by, 3, 3);
        }
        g.setColor(new Color(90, 65, 40));
        g.drawRect(x, y, size, size);
        g.setColor(new Color(255, 255, 255, 40));
        g.drawRect(x + 1, y + 1, size - 2, size - 2);
    }

    // ==================== СОЗДАНИЕ МИРА ====================
    private void drawWorldCreate(Graphics2D g) {
        drawMenuBackground(g);
        g.setColor(new Color(0, 0, 0, 160));
        g.fillRect(0, 0, SCREEN_W, SCREEN_H);

        g.setFont(PixelFont.font(38, Font.BOLD));
        drawCenteredWithPixelShadow(g, "Создание мира", SCREEN_W / 2, 55, new Color(255, 220, 80));

        g.setFont(PixelFont.font(16, Font.PLAIN));
        g.setColor(Color.WHITE);
        drawCentered(g, "Сид (пусто = случайный):", SCREEN_W / 2, 110);

        int bx = SCREEN_W / 2 - 250;
        int by = 130;
        g.setColor(new Color(0, 0, 0, 220));
        g.fillRect(bx - 3, by - 3, 506, 46);
        g.setColor(typingSeed ? new Color(255, 240, 100) : new Color(150, 150, 180));
        g.drawRect(bx - 2, by - 2, 504, 44);
        g.setColor(new Color(30, 30, 50));
        g.fillRect(bx, by, 500, 40);
        g.setColor(Color.WHITE);
        g.setFont(PixelFont.font(18, Font.BOLD));
        String shown = inputSeed.isEmpty() ? "_" : inputSeed + (typingSeed ? "_" : "");
        g.drawString(shown, bx + 12, by + 27);

        String[] tabs = {"Размер", "Тип", "Сложность", "Ресурсы"};
        int tabW = 130;
        int tabX = SCREEN_W / 2 - (tabs.length * tabW) / 2;
        int tabY = 200;
        for (int i = 0; i < tabs.length; i++) {
            int tx = tabX + i * tabW;
            boolean active = worldSettingsTab == i;
            boolean hover = mouseY > tabY && mouseY < tabY + 40 && mouseX > tx && mouseX < tx + tabW - 6;
            g.setColor(active ? new Color(180, 140, 60) : (hover ? new Color(100, 80, 50) : new Color(60, 50, 40)));
            g.fillRect(tx, tabY, tabW - 6, 40);
            g.setColor(active ? new Color(255, 220, 100) : new Color(150, 130, 100));
            g.drawRect(tx, tabY, tabW - 6, 40);
            g.setColor(active ? Color.WHITE : new Color(200, 200, 200));
            g.setFont(PixelFont.font(14, Font.BOLD));
            FontMetrics fm = g.getFontMetrics();
            g.drawString(tabs[i], tx + (tabW - 6 - fm.stringWidth(tabs[i])) / 2, tabY + 25);
        }

        int contX = SCREEN_W / 2 - 300;
        int contY = 260;
        int contW = 600;
        int contH = 300;
        drawPixelPanel(g, contX, contY, contW, contH);

        if (worldSettingsTab == 0) {
            g.setFont(PixelFont.font(16, Font.BOLD));
            g.setColor(Color.WHITE);
            g.drawString("Ширина: " + newWorldWidth, contX + 20, contY + 40);
            g.setColor(new Color(180, 200, 240));
            g.fillRect(contX + 20, contY + 50, 560, 20);
            g.setColor(new Color(100, 150, 220));
            g.fillRect(contX + 20, contY + 50, (int) (560 * (newWorldWidth - 200) / 1800.0), 20);

            g.setColor(Color.WHITE);
            g.drawString("Высота: " + newWorldHeight, contX + 20, contY + 140);
            g.setColor(new Color(180, 200, 240));
            g.fillRect(contX + 20, contY + 150, 560, 20);
            g.setColor(new Color(100, 150, 220));
            g.fillRect(contX + 20, contY + 150, (int) (560 * (newWorldHeight - 100) / 300.0), 20);

            drawMCButton(g, "-100", contX + 20, contY + 90, 70, 35,
                    mouseY > contY + 90 && mouseY < contY + 125 && mouseX > contX + 20 && mouseX < contX + 90);
            drawMCButton(g, "+100", contX + 100, contY + 90, 70, 35,
                    mouseY > contY + 90 && mouseY < contY + 125 && mouseX > contX + 100 && mouseX < contX + 170);
            drawMCButton(g, "-100", contX + 20, contY + 190, 70, 35,
                    mouseY > contY + 190 && mouseY < contY + 225 && mouseX > contX + 20 && mouseX < contX + 90);
            drawMCButton(g, "+100", contX + 100, contY + 190, 70, 35,
                    mouseY > contY + 190 && mouseY < contY + 225 && mouseX > contX + 100 && mouseX < contX + 170);
        } else if (worldSettingsTab == 1) {
            g.setFont(PixelFont.font(16, Font.BOLD));
            g.setColor(Color.WHITE);
            g.drawString("Выберите тип мира:", contX + 20, contY + 30);

            WorldType[] types = WorldType.values();
            int cols = 3, btnW = 170, btnH = 45, gap = 15;
            for (int i = 0; i < types.length; i++) {
                int cx = contX + 20 + (i % cols) * (btnW + gap);
                int cy = contY + 50 + (i / cols) * (btnH + gap);
                boolean sel = newWorldType == types[i];
                boolean hover = mouseY > cy && mouseY < cy + btnH && mouseX > cx && mouseX < cx + btnW;
                g.setColor(sel ? new Color(180, 140, 60) : (hover ? new Color(100, 80, 50) : new Color(60, 50, 40)));
                g.fillRect(cx, cy, btnW, btnH);
                g.setColor(sel ? new Color(255, 220, 100) : new Color(120, 90, 60));
                g.drawRect(cx, cy, btnW, btnH);
                g.setColor(sel ? Color.WHITE : new Color(200, 200, 200));
                g.setFont(PixelFont.font(14, Font.BOLD));
                FontMetrics fm = g.getFontMetrics();
                g.drawString(types[i].displayName,
                        cx + (btnW - fm.stringWidth(types[i].displayName)) / 2, cy + 29);
            }
        } else if (worldSettingsTab == 2) {
            g.setFont(PixelFont.font(16, Font.BOLD));
            g.setColor(Color.WHITE);
            g.drawString("Режим игры:", contX + 20, contY + 30);

            GameMode[] modes = GameMode.values();
            String[] modeNames = {"Выживание", "Креатив", "Хардкор"};
            for (int i = 0; i < modes.length; i++) {
                int cx = contX + 20 + i * 190;
                int cy = contY + 50;
                boolean sel = newWorldMode == modes[i];
                boolean hover = mouseY > cy && mouseY < cy + 45 && mouseX > cx && mouseX < cx + 170;
                g.setColor(sel ? new Color(180, 60, 60) : (hover ? new Color(100, 50, 50) : new Color(60, 40, 40)));
                g.fillRect(cx, cy, 170, 45);
                g.setColor(sel ? new Color(255, 200, 100) : new Color(120, 80, 60));
                g.drawRect(cx, cy, 170, 45);
                g.setColor(Color.WHITE);
                g.setFont(PixelFont.font(14, Font.BOLD));
                FontMetrics fm = g.getFontMetrics();
                g.drawString(modeNames[i], cx + (170 - fm.stringWidth(modeNames[i])) / 2, cy + 29);
            }

            g.setFont(PixelFont.font(16, Font.BOLD));
            g.setColor(Color.WHITE);
            g.drawString("Сложность:", contX + 20, contY + 140);

            Difficulty[] diffs = Difficulty.values();
            for (int i = 0; i < diffs.length; i++) {
                int cx = contX + 20 + i * 145;
                int cy = contY + 160;
                boolean sel = newWorldDifficulty == diffs[i];
                boolean hover = mouseY > cy && mouseY < cy + 45 && mouseX > cx && mouseX < cx + 135;
                g.setColor(sel ? new Color(140, 100, 40) : (hover ? new Color(80, 60, 40) : new Color(50, 40, 30)));
                g.fillRect(cx, cy, 135, 45);
                g.setColor(sel ? new Color(255, 220, 100) : new Color(120, 90, 60));
                g.drawRect(cx, cy, 135, 45);
                g.setColor(Color.WHITE);
                g.setFont(PixelFont.font(13, Font.BOLD));
                FontMetrics fm = g.getFontMetrics();
                g.drawString(diffs[i].displayName,
                        cx + (135 - fm.stringWidth(diffs[i].displayName)) / 2, cy + 29);
            }
        } else if (worldSettingsTab == 3) {
            g.setFont(PixelFont.font(16, Font.BOLD));
            g.setColor(Color.WHITE);
            g.drawString("Плотность руды: " + (int) (newWorldOreDensity * 100) + "%", contX + 20, contY + 40);
            g.fillRect(contX + 300, contY + 25, 260, 20);
            g.setColor(new Color(80, 140, 220));
            g.fillRect(contX + 300, contY + 25, (int) (260 * newWorldOreDensity / 3.0), 20);

            g.setColor(Color.WHITE);
            g.drawString("Плотность деревьев: " + (int) (newWorldTreeDensity * 100) + "%", contX + 20, contY + 90);
            g.fillRect(contX + 300, contY + 75, 260, 20);
            g.setColor(new Color(80, 200, 80));
            g.fillRect(contX + 300, contY + 75, (int) (260 * newWorldTreeDensity / 3.0), 20);

            g.setColor(Color.WHITE);
            g.drawString("Монстров: " + (int) (newWorldMonsterRate * 100) + "%", contX + 20, contY + 140);
            g.fillRect(contX + 300, contY + 125, 260, 20);
            g.setColor(new Color(220, 80, 80));
            g.fillRect(contX + 300, contY + 125, (int) (260 * newWorldMonsterRate / 3.0), 20);

            g.setColor(Color.WHITE);
            g.drawString("Структуры: " + (newWorldStructures ? "ВКЛ" : "ВЫКЛ"), contX + 20, contY + 190);
            drawMCButton(g, newWorldStructures ? "Выкл" : "Вкл", contX + 400, contY + 175, 160, 35,
                    mouseY > contY + 175 && mouseY < contY + 210 && mouseX > contX + 400 && mouseX < contX + 560);
        }

        drawMCButton(g, "Создать мир [Enter]", SCREEN_W / 2 - 220, SCREEN_H - 90, 440, 55,
                mouseY > SCREEN_H - 90 && mouseY < SCREEN_H - 35 && mouseX > SCREEN_W / 2 - 220 && mouseX < SCREEN_W / 2 + 220);
        drawMCButton(g, "Отмена [Esc]", SCREEN_W / 2 - 150, SCREEN_H - 30, 300, 25,
                mouseY > SCREEN_H - 30 && mouseY < SCREEN_H - 5 && mouseX > SCREEN_W / 2 - 150 && mouseX < SCREEN_W / 2 + 150);
    }

    // ==================== НАСТРОЙКИ ====================
    private void drawSettings(Graphics2D g) {
        drawMenuBackground(g);
        g.setColor(new Color(0, 0, 0, 160));
        g.fillRect(0, 0, SCREEN_W, SCREEN_H);

        g.setFont(PixelFont.font(42, Font.BOLD));
        drawCenteredWithPixelShadow(g, "Настройки", SCREEN_W / 2, 45, new Color(255, 220, 80));

        String[] tabs = {"Игра", "Звук", "Прочее"};
        int tabW = 200;
        int tabX = SCREEN_W / 2 - (tabs.length * tabW) / 2;
        int tabY = 80;
        for (int i = 0; i < tabs.length; i++) {
            int tx = tabX + i * tabW;
            boolean active = settingsTab == i;
            boolean hover = mouseY > tabY && mouseY < tabY + 42 && mouseX > tx && mouseX < tx + tabW - 6;
            g.setColor(active ? new Color(180, 140, 60) : (hover ? new Color(100, 80, 50) : new Color(60, 50, 40)));
            g.fillRect(tx, tabY, tabW - 6, 42);
            g.setColor(active ? new Color(255, 220, 100) : new Color(150, 130, 100));
            g.drawRect(tx, tabY, tabW - 6, 42);
            g.setColor(active ? Color.WHITE : new Color(200, 200, 200));
            g.setFont(PixelFont.font(16, Font.BOLD));
            FontMetrics fm = g.getFontMetrics();
            g.drawString(tabs[i], tx + (tabW - 6 - fm.stringWidth(tabs[i])) / 2, tabY + 27);
        }

        int cx = 100, cy = 140, cw = SCREEN_W - 200, ch = 480;
        drawPixelPanel(g, cx, cy, cw, ch);

        if (settingsTab == 0) {
            g.setFont(PixelFont.font(20, Font.BOLD));
            g.setColor(new Color(255, 220, 100));
            g.drawString("Настройки игры", cx + 20, cy + 35);

            g.setFont(PixelFont.font(14, Font.PLAIN));
            g.setColor(Color.WHITE);
            g.drawString("Показывать FPS:", cx + 20, cy + 90);
            drawMCButton(g, showFPS ? "ВКЛ" : "ВЫКЛ", cx + 300, cy + 70, 140, 32,
                    mouseY > cy + 70 && mouseY < cy + 102 && mouseX > cx + 300 && mouseX < cx + 440);

            g.drawString("Показывать координаты:", cx + 20, cy + 140);
            drawMCButton(g, showCoordinates ? "ВКЛ" : "ВЫКЛ", cx + 300, cy + 120, 140, 32,
                    mouseY > cy + 120 && mouseY < cy + 152 && mouseX > cx + 300 && mouseX < cx + 440);

            g.drawString("Автосохранение:", cx + 20, cy + 190);
            drawMCButton(g, autoSave ? "ВКЛ" : "ВЫКЛ", cx + 300, cy + 170, 140, 32,
                    mouseY > cy + 170 && mouseY < cy + 202 && mouseX > cx + 300 && mouseX < cx + 440);

            g.setColor(new Color(180, 200, 240));
            g.drawString("Сложность: " + difficulty.displayName, cx + 20, cy + 250);
            g.drawString("Режим: " + mode, cx + 20, cy + 275);
        } else if (settingsTab == 1) {
            g.setFont(PixelFont.font(20, Font.BOLD));
            g.setColor(new Color(255, 220, 100));
            g.drawString("Звук и музыка", cx + 20, cy + 35);

            g.setFont(PixelFont.font(14, Font.PLAIN));
            g.setColor(Color.WHITE);
            g.drawString("Музыка: " + (int) (musicVolume * 100) + "%", cx + 20, cy + 100);
            g.setColor(new Color(60, 40, 90));
            g.fillRect(cx + 300, cy + 85, 300, 20);
            g.setColor(new Color(140, 80, 220));
            g.fillRect(cx + 300, cy + 85, (int) (300 * musicVolume), 20);
            drawMCButton(g, "-", cx + 620, cy + 80, 40, 32,
                    mouseY > cy + 80 && mouseY < cy + 112 && mouseX > cx + 620 && mouseX < cx + 660);
            drawMCButton(g, "+", cx + 670, cy + 80, 40, 32,
                    mouseY > cy + 80 && mouseY < cy + 112 && mouseX > cx + 670 && mouseX < cx + 710);

            g.setColor(Color.WHITE);
            g.drawString("Звуки: " + (int) (sfxVolume * 100) + "%", cx + 20, cy + 160);
            g.setColor(new Color(60, 90, 40));
            g.fillRect(cx + 300, cy + 145, 300, 20);
            g.setColor(new Color(120, 200, 80));
            g.fillRect(cx + 300, cy + 145, (int) (300 * sfxVolume), 20);
            drawMCButton(g, "-", cx + 620, cy + 140, 40, 32,
                    mouseY > cy + 140 && mouseY < cy + 172 && mouseX > cx + 620 && mouseX < cx + 660);
            drawMCButton(g, "+", cx + 670, cy + 140, 40, 32,
                    mouseY > cy + 140 && mouseY < cy + 172 && mouseX > cx + 670 && mouseX < cx + 710);
        } else {
            g.setFont(PixelFont.font(20, Font.BOLD));
            g.setColor(new Color(255, 220, 100));
            g.drawString("Прочее", cx + 20, cy + 35);

            g.setFont(PixelFont.font(14, Font.PLAIN));
            g.setColor(Color.WHITE);
            g.drawString("Версия: " + VERSION, cx + 20, cy + 90);

            g.setColor(new Color(200, 220, 240));
            g.setFont(PixelFont.font(12, Font.PLAIN));
            g.drawString("A/D — движение · Space — прыжок", cx + 40, cy + 130);
            g.drawString("ЛКМ — копать/атаковать · ПКМ — ставить/открыть", cx + 40, cy + 150);
            g.drawString("E — инвентарь · T — чат · M — режим", cx + 40, cy + 170);
            g.drawString("F5 — сохранить · F11 — полный экран", cx + 40, cy + 190);
        }

        drawMCButton(g, "Сохранить [S]", SCREEN_W / 2 - 320, SCREEN_H - 60, 300, 45,
                mouseY > SCREEN_H - 60 && mouseY < SCREEN_H - 15 && mouseX > SCREEN_W / 2 - 320 && mouseX < SCREEN_W / 2 - 20);
        drawMCButton(g, "Назад [Esc]", SCREEN_W / 2 + 20, SCREEN_H - 60, 300, 45,
                mouseY > SCREEN_H - 60 && mouseY < SCREEN_H - 15 && mouseX > SCREEN_W / 2 + 20 && mouseX < SCREEN_W / 2 + 320);
    }

    // ==================== ДОСТИЖЕНИЯ ====================
    private void drawAchievements(Graphics2D g) {
        drawMenuBackground(g);
        g.setColor(new Color(0, 0, 0, 160));
        g.fillRect(0, 0, SCREEN_W, SCREEN_H);

        g.setFont(PixelFont.font(42, Font.BOLD));
        drawCenteredWithPixelShadow(g, "Достижения", SCREEN_W / 2, 50, new Color(255, 220, 80));

        int unlockedCount = 0;
        for (Achievement a : achievements) {
            if (a.unlocked) {
                unlockedCount++;
            }
        }

        g.setFont(PixelFont.font(16, Font.BOLD));
        g.setColor(new Color(255, 220, 100));
        drawCentered(g, "Открыто: " + unlockedCount + " / " + achievements.size(), SCREEN_W / 2, 90);

        int px = 60, py = 120, colW = 400, rowH = 52;
        int col = 0, row = 0;
        for (Achievement a : achievements) {
            int x = px + col * colW;
            int y = py + row * rowH;

            g.setColor(a.unlocked ? new Color(40, 80, 40, 220) : new Color(30, 30, 45, 220));
            g.fillRect(x, y, colW - 20, rowH - 8);
            g.setColor(a.unlocked ? new Color(120, 220, 120) : new Color(90, 90, 120));
            g.drawRect(x, y, colW - 20, rowH - 8);

            g.setColor(a.unlocked ? new Color(255, 240, 100) : new Color(180, 180, 200));
            g.setFont(PixelFont.font(14, Font.BOLD));
            g.drawString((a.unlocked ? "★ " : "☆ ") + a.title, x + 12, y + 20);

            g.setColor(Color.WHITE);
            g.setFont(PixelFont.font(11, Font.PLAIN));
            g.drawString(a.description, x + 12, y + 36);

            row++;
            if (row >= 9) {
                row = 0;
                col++;
            }
        }

        drawMCButton(g, "Назад [Esc]", SCREEN_W / 2 - 150, SCREEN_H - 60, 300, 45,
                mouseY > SCREEN_H - 60 && mouseY < SCREEN_H - 15 && mouseX > SCREEN_W / 2 - 150 && mouseX < SCREEN_W / 2 + 150);
    }

    // ==================== МУЛЬТИПЛЕЕР ====================
    private void drawMultiplayer(Graphics2D g) {
        drawMenuBackground(g);
        g.setColor(new Color(0, 0, 0, 160));
        g.fillRect(0, 0, SCREEN_W, SCREEN_H);

        g.setFont(PixelFont.font(42, Font.BOLD));
        drawCenteredWithPixelShadow(g, "Мультиплеер", SCREEN_W / 2, 60, new Color(255, 220, 80));

        g.setFont(PixelFont.font(16, Font.PLAIN));
        g.setColor(Color.WHITE);
        drawCentered(g, "Адрес сервера:", SCREEN_W / 2, 140);

        int bx = SCREEN_W / 2 - 250;
        int by = 165;
        g.setColor(new Color(0, 0, 0, 220));
        g.fillRect(bx - 3, by - 3, 506, 46);
        g.setColor(typingMpAddress ? new Color(255, 240, 100) : new Color(150, 150, 180));
        g.drawRect(bx - 2, by - 2, 504, 44);
        g.setColor(new Color(30, 30, 50));
        g.fillRect(bx, by, 500, 40);
        g.setColor(Color.WHITE);
        g.setFont(PixelFont.font(18, Font.BOLD));
        String shown = mpAddress.isEmpty() ? "_" : mpAddress + (typingMpAddress ? "_" : "");
        g.drawString(shown, bx + 12, by + 27);

        drawMCButton(g, "Создать сервер (хост)", SCREEN_W / 2 - 220, 250, 440, 55,
                mouseY > 250 && mouseY < 305 && mouseX > SCREEN_W / 2 - 220 && mouseX < SCREEN_W / 2 + 220);
        drawMCButton(g, "Подключиться", SCREEN_W / 2 - 220, 320, 440, 55,
                mouseY > 320 && mouseY < 375 && mouseX > SCREEN_W / 2 - 220 && mouseX < SCREEN_W / 2 + 220);
        drawMCButton(g, "Назад [Esc]", SCREEN_W / 2 - 150, SCREEN_H - 70, 300, 50,
                mouseY > SCREEN_H - 70 && mouseY < SCREEN_H - 20 && mouseX > SCREEN_W / 2 - 150 && mouseX < SCREEN_W / 2 + 150);

        g.setFont(PixelFont.font(12, Font.PLAIN));
        g.setColor(new Color(180, 200, 240));
        drawCentered(g, "Порт " + MP_PORT + ". Хост запускает сервер, клиенты вводят IP.", SCREEN_W / 2, 450);
        if (!mpStatus.isEmpty()) {
            g.setColor(new Color(255, 220, 100));
            drawCentered(g, mpStatus, SCREEN_W / 2, 500);
        }
    }

    private void drawMpHostWaiting(Graphics2D g) {
        drawMenuBackground(g);
        g.setColor(new Color(0, 0, 0, 160));
        g.fillRect(0, 0, SCREEN_W, SCREEN_H);

        g.setFont(PixelFont.font(36, Font.BOLD));
        drawCenteredWithPixelShadow(g, "Сервер запущен", SCREEN_W / 2, 100, new Color(120, 255, 120));

        g.setFont(PixelFont.font(18, Font.PLAIN));
        g.setColor(Color.WHITE);
        drawCentered(g, "Порт: " + MP_PORT, SCREEN_W / 2, 160);
        drawCentered(g, "Ожидание игроков...", SCREEN_W / 2, 200);

        int dots = (int) (System.currentTimeMillis() / 300) % 4;
        g.setFont(PixelFont.font(24, Font.BOLD));
        g.setColor(new Color(200, 240, 200));
        drawCentered(g, ".".repeat(dots), SCREEN_W / 2, 240);

        g.setFont(PixelFont.font(16, Font.BOLD));
        g.setColor(new Color(255, 220, 100));
        drawCentered(g, "Игроков: " + (mpPlayerList.size() + 1), SCREEN_W / 2, 320);

        g.setFont(PixelFont.font(14, Font.PLAIN));
        g.setColor(Color.WHITE);
        int y = 360;
        g.drawString("★ Хост (вы)", SCREEN_W / 2 - 100, y);
        y += 25;
        for (String p : mpPlayerList) {
            g.drawString("• " + p, SCREEN_W / 2 - 100, y);
            y += 25;
        }

        drawMCButton(g, "Начать игру [Enter]", SCREEN_W / 2 - 220, SCREEN_H - 120, 440, 55,
                mouseY > SCREEN_H - 120 && mouseY < SCREEN_H - 65 && mouseX > SCREEN_W / 2 - 220 && mouseX < SCREEN_W / 2 + 220);
        drawMCButton(g, "Отменить [Esc]", SCREEN_W / 2 - 150, SCREEN_H - 55, 300, 45,
                mouseY > SCREEN_H - 55 && mouseY < SCREEN_H - 10 && mouseX > SCREEN_W / 2 - 150 && mouseX < SCREEN_W / 2 + 150);
    }

    private void drawLoading(Graphics2D g) {
        g.setColor(Color.BLACK);
        g.fillRect(0, 0, SCREEN_W, SCREEN_H);
        g.setColor(Color.WHITE);
        g.setFont(PixelFont.font(32, Font.BOLD));
        drawCentered(g, "Загрузка мира...", SCREEN_W / 2, SCREEN_H / 2 - 40);
        g.setFont(PixelFont.font(14, Font.PLAIN));
        g.setColor(new Color(180, 200, 240));
        drawCentered(g, mpStatus, SCREEN_W / 2, SCREEN_H / 2 + 10);

        int cx = SCREEN_W / 2 - 60;
        int cy = SCREEN_H / 2 + 60;
        int dots = (int) (System.currentTimeMillis() / 300) % 4;
        for (int i = 0; i < 4; i++) {
            g.setColor(i <= dots ? Color.WHITE : new Color(80, 80, 100));
            g.fillRect(cx + i * 30, cy, 20, 20);
        }
    }

    private void drawResourcePacks(Graphics2D g) {
        drawMenuBackground(g);
        g.setColor(new Color(0, 0, 0, 160));
        g.fillRect(0, 0, SCREEN_W, SCREEN_H);

        g.setFont(PixelFont.font(42, Font.BOLD));
        drawCenteredWithPixelShadow(g, "Ресурспаки", SCREEN_W / 2, 50, new Color(255, 220, 80));

        drawPixelPanel(g, 60, 110, SCREEN_W - 120, 380);

        g.setFont(PixelFont.font(16, Font.BOLD));
        g.setColor(Color.WHITE);
        g.drawString("Доступные ресурспаки:", 80, 140);

        int listY = 160, itemH = 60;
        for (int i = 0; i < Math.min(resourcePacks.size(), 5); i++) {
            ResourcePack rp = resourcePacks.get(i);
            int y = listY + i * itemH;
            boolean sel = i == selectedPackIndex;
            boolean hover = mouseY > y && mouseY < y + itemH - 6 && mouseX > 80 && mouseX < SCREEN_W - 100;

            g.setColor(sel ? new Color(80, 120, 60, 220) : (hover ? new Color(60, 60, 50, 220) : new Color(40, 40, 35, 220)));
            g.fillRect(80, y, SCREEN_W - 180, itemH - 6);
            g.setColor(sel ? new Color(160, 255, 160) : new Color(120, 120, 90));
            g.drawRect(80, y, SCREEN_W - 180, itemH - 6);

            g.setColor(rp.isDefault ? new Color(80, 120, 60) : new Color(60, 90, 140));
            g.fillRect(90, y + 8, 40, 40);
            g.setColor(new Color(200, 220, 240));
            g.drawRect(90, y + 8, 40, 40);

            g.setColor(sel ? Color.WHITE : new Color(220, 220, 220));
            g.setFont(PixelFont.font(16, Font.BOLD));
            g.drawString(rp.name, 145, y + 25);

            g.setColor(new Color(180, 180, 200));
            g.setFont(PixelFont.font(11, Font.PLAIN));
            String desc = rp.description.isEmpty() ? "Без описания" : rp.description;
            g.drawString(desc, 145, y + 43);

            if (rp.active) {
                g.setColor(new Color(120, 255, 120));
                g.setFont(PixelFont.font(12, Font.BOLD));
                g.drawString("✓ Активен", SCREEN_W - 220, y + 25);
            }
        }

        int btnY = 510;
        drawMCButton(g, "Применить", 60, btnY, 180, 42,
                mouseY > btnY && mouseY < btnY + 42 && mouseX > 60 && mouseX < 240);
        drawMCButton(g, "Отключить", 250, btnY, 180, 42,
                mouseY > btnY && mouseY < btnY + 42 && mouseX > 250 && mouseX < 430);
        drawMCButton(g, "Загрузить .zip", 440, btnY, 230, 42,
                mouseY > btnY && mouseY < btnY + 42 && mouseX > 440 && mouseX < 670);
        drawMCButton(g, "Открыть папку", 680, btnY, 200, 42,
                mouseY > btnY && mouseY < btnY + 42 && mouseX > 680 && mouseX < 880);
        drawMCButton(g, "Обновить [R]", 890, btnY, 180, 42,
                mouseY > btnY && mouseY < btnY + 42 && mouseX > 890 && mouseX < 1070);

        drawMCButton(g, "Назад [Esc]", SCREEN_W / 2 - 150, SCREEN_H - 55, 300, 45,
                mouseY > SCREEN_H - 55 && mouseY < SCREEN_H - 10 && mouseX > SCREEN_W / 2 - 150 && mouseX < SCREEN_W / 2 + 150);
    }
    // ==================== РЕНДЕР ИГРЫ ====================

    private void drawGame(Graphics2D g) {
        if (world == null || player == null) {
            return;
        }
        if (world.getWidth() <= 10) {
            state = GameState.LOADING;
            return;
        }

        int camX = (int) player.cameraX;
        int camY = (int) player.cameraY;

        drawSky(g);
        if (isNight()) {
            drawStars(g);
        }
        drawCelestialBody(g);
        drawClouds(g, camX);
        drawWeather(g, camX, camY);

        int startX = Math.max(0, camX / TILE);
        int startY = Math.max(0, camY / TILE);
        int endX = Math.min(world.getWidth() - 1, (camX + SCREEN_W) / TILE + 1);
        int endY = Math.min(world.getHeight() - 1, (camY + SCREEN_H) / TILE + 1);

        for (int y = startY; y <= endY; y++) {
            for (int x = startX; x <= endX; x++) {
                int bg = world.getBackground(x, y);
                if (bg == World.AIR) {
                    continue;
                }
                int px = x * TILE - camX;
                int py = y * TILE - camY;
                if (Modules.SHOW_BACKGROUND) {
                    BufferedImage bgImg = Textures.get(bg);
                    g.drawImage(bgImg, px, py, null);
                    g.setColor(new Color(0, 0, 0, 100));
                    g.fillRect(px, py, TILE, TILE);
                }
            }
        }

        for (int y = startY; y <= endY; y++) {
            for (int x = startX; x <= endX; x++) {
                int b = world.getBlock(x, y);
                if (b == World.AIR) {
                    continue;
                }
                int px = x * TILE - camX;
                int py = y * TILE - camY;

                if (world.getBlock(x, y + 1) == World.AIR) {
                    g.setColor(new Color(0, 0, 0, 60));
                    g.fillRect(px, py + TILE, TILE, 4);
                }
                if (world.getBlock(x + 1, y) == World.AIR) {
                    g.setColor(new Color(0, 0, 0, 40));
                    g.fillRect(px + TILE, py, 3, TILE);
                }
                g.drawImage(Textures.get(b), px, py, null);
            }
        }

        for (Villager v : villagers) {
            v.draw(g, camX, camY);
        }
        for (Animal a : animals) {
            a.draw(g, camX, camY);
        }
        for (RemotePlayer rp : remotePlayers) {
            rp.draw(g, camX, camY);
        }
        for (Monster m : monsters) {
            m.draw(g, camX, camY);
        }
        for (Arrow ar : arrows) {
            ar.draw(g, camX, camY);
        }
        player.draw(g, camX, camY);

        if (digX >= 0 && digProgress > 0) {
            int px = digX * TILE - camX;
            int py = digY * TILE - camY;
            g.setColor(new Color(0, 0, 0, 180));
            g.fillRect(px + 4, py - 10, TILE - 8, 6);
            g.setColor(new Color(200, 255, 100));
            double ratio = Math.min(1.0, digProgress / (double) digRequired);
            int w = (int) ((TILE - 8) * ratio);
            g.fillRect(px + 4, py - 10, w, 6);
        }

        g.setFont(PixelFont.font(12, Font.BOLD));
        for (FloatingText ft : floaters) {
            g.setColor(new Color(0, 0, 0, 220));
            g.drawString(ft.text, (int) (ft.x - camX) + 1, (int) (ft.y - camY) + 1);
            g.setColor(ft.color);
            g.drawString(ft.text, (int) (ft.x - camX), (int) (ft.y - camY));
        }

        drawCrosshair(g, camX, camY);
        drawHUD(g);
        if (inventoryOpen) {
            drawInventory(g);
        }
        if (activeContainer != null) {
            drawContainer(g);
        }
        drawChat(g);

        if (draggedStack != null) {
            BufferedImage ic = Textures.get(draggedStack.id);
            g.drawImage(ic, mouseX - 20, mouseY - 20, 40, 40, null);
            if (draggedStack.count > 1) {
                g.setFont(PixelFont.font(13, Font.BOLD));
                g.setColor(Color.BLACK);
                g.drawString("" + draggedStack.count, mouseX + 4, mouseY + 20);
                g.setColor(Color.WHITE);
                g.drawString("" + draggedStack.count, mouseX + 3, mouseY + 19);
            }
        }
    }

    private void drawSky(Graphics2D g) {
        double t = dayProgress();
        Color skyTop, skyBot;
        switch (currentWorldType) {
            case NETHER:
                skyTop = new Color(90, 20, 20);
                skyBot = new Color(50, 10, 10);
                break;
            case HEAVEN:
                skyTop = new Color(255, 250, 200);
                skyBot = new Color(255, 220, 250);
                break;
            case CAVE:
                skyTop = new Color(10, 10, 15);
                skyBot = new Color(20, 20, 25);
                break;
            default:
                if (t < 0.25) {
                    skyTop = new Color(255, 140, 80);
                    skyBot = new Color(255, 200, 140);
                } else if (t < 0.5) {
                    skyTop = new Color(100, 170, 240);
                    skyBot = new Color(180, 220, 255);
                } else if (t < 0.75) {
                    skyTop = new Color(240, 110, 70);
                    skyBot = new Color(200, 130, 130);
                } else {
                    skyTop = new Color(10, 10, 40);
                    skyBot = new Color(25, 25, 60);
                }
        }
        g.setPaint(new GradientPaint(0, 0, skyTop, 0, SCREEN_H, skyBot));
        g.fillRect(0, 0, SCREEN_W, SCREEN_H);
    }

    private void drawStars(Graphics2D g) {
        Random rnd = new Random(999);
        for (int i = 0; i < 80; i++) {
            int sx = rnd.nextInt(SCREEN_W);
            int sy = rnd.nextInt(SCREEN_H / 2);
            int b = 150 + rnd.nextInt(100);
            g.setColor(new Color(b, b, b, 200));
            g.fillRect(sx, sy, 2, 2);
        }
    }

    private void drawCelestialBody(Graphics2D g) {
        if (currentWorldType == WorldType.CAVE || currentWorldType == WorldType.NETHER) {
            return;
        }
        double t = dayProgress();
        int sunX = (int) (SCREEN_W * t * 2);
        if (sunX > SCREEN_W) {
            sunX = SCREEN_W * 2 - sunX;
        }
        int sunY = (int) (SCREEN_H * 0.15 + Math.sin(t * Math.PI * 2) * 100);
        if (isNight()) {
            g.setColor(new Color(240, 240, 220));
            g.fillRect(sunX - 24, sunY, 48, 48);
            g.setColor(new Color(10, 10, 40));
            g.fillRect(sunX - 8, sunY, 32, 48);
        } else {
            g.setColor(new Color(255, 240, 130));
            g.fillRect(sunX - 24, sunY, 48, 48);
            g.setColor(new Color(255, 220, 80));
            g.drawRect(sunX - 24, sunY, 48, 48);
        }
    }

    private void drawClouds(Graphics2D g, int camX) {
        if (currentWorldType == WorldType.CAVE || currentWorldType == WorldType.NETHER) {
            return;
        }
        long t = System.currentTimeMillis() / 100;
        Random rnd = new Random(555);
        for (int i = 0; i < 8; i++) {
            int cx = (int) ((rnd.nextInt(2000) - (t + camX / 3) % 2000) + SCREEN_W);
            int cy = 30 + rnd.nextInt(80);
            int cw = 60 + rnd.nextInt(60);
            int ch = 20 + rnd.nextInt(10);
            g.setColor(new Color(255, 255, 255, 180));
            g.fillRect(cx, cy, cw, ch);
            g.fillRect(cx + cw / 4, cy - ch / 2, cw / 2, ch / 2);
        }
    }

    private void drawWeather(Graphics2D g, int camX, int camY) {
        if (weather == Weather.CLEAR) {
            return;
        }
        long t = System.currentTimeMillis();
        Random rnd = new Random(t / 50);

        if (weather == Weather.RAIN || weather == Weather.STORM) {
            g.setColor(new Color(50, 80, 120, 60));
            g.fillRect(0, 0, SCREEN_W, SCREEN_H);
            int count = weather == Weather.STORM ? 200 : 100;
            for (int i = 0; i < count; i++) {
                int rx = rnd.nextInt(SCREEN_W);
                int ry = (rnd.nextInt(SCREEN_H) + (int) (t / 4) % SCREEN_H) % SCREEN_H;
                g.setColor(new Color(180, 200, 240, 180));
                g.fillRect(rx, ry, 1, 6);
            }
            if (weather == Weather.STORM && rnd.nextInt(100) < 3) {
                g.setColor(new Color(255, 255, 255, 200));
                g.fillRect(0, 0, SCREEN_W, SCREEN_H);
            }
        } else if (weather == Weather.SNOW) {
            for (int i = 0; i < 80; i++) {
                int rx = rnd.nextInt(SCREEN_W);
                int ry = (rnd.nextInt(SCREEN_H) + (int) (t / 8) % SCREEN_H) % SCREEN_H;
                g.setColor(new Color(255, 255, 255, 220));
                g.fillRect(rx, ry, 2, 2);
            }
        } else if (weather == Weather.SANDSTORM) {
            g.setColor(new Color(200, 170, 100, 100));
            g.fillRect(0, 0, SCREEN_W, SCREEN_H);
            for (int i = 0; i < 100; i++) {
                int rx = (rnd.nextInt(SCREEN_W) + (int) (t / 3)) % SCREEN_W;
                int ry = rnd.nextInt(SCREEN_H);
                g.setColor(new Color(220, 190, 130, 180));
                g.fillRect(rx, ry, 3, 1);
            }
        }
    }

    private void drawCrosshair(Graphics2D g, int camX, int camY) {
        int wx = (int) ((mouseX + camX) / TILE);
        int wy = (int) ((mouseY + camY) / TILE);
        int cx = wx * TILE - camX;
        int cy = wy * TILE - camY;
        g.setColor(new Color(255, 255, 255, 220));
        for (int i = 0; i < TILE; i += 4) {
            g.fillRect(cx + i, cy, 2, 2);
            g.fillRect(cx + i, cy + TILE - 2, 2, 2);
            g.fillRect(cx, cy + i, 2, 2);
            g.fillRect(cx + TILE - 2, cy + i, 2, 2);
        }
    }

    // ==================== HUD ====================
    private void drawHUD(Graphics2D g) {
        int hearts = 10;
        double hpPerHeart = player.maxHp / (double) hearts;
        for (int i = 0; i < hearts; i++) {
            int hx = 12 + i * 22;
            int hy = 12;
            double hpInHeart = Math.max(0, Math.min(hpPerHeart, player.hp - i * hpPerHeart));
            drawPixelHeart(g, hx, hy, hpInHeart / hpPerHeart);
        }

        int armorValue = player.getArmorPoints();
        if (armorValue > 0) {
            g.setFont(PixelFont.font(12, Font.BOLD));
            g.setColor(new Color(0, 0, 0, 200));
            g.fillRect(12, 40, 100, 18);
            g.setColor(new Color(200, 220, 240));
            g.drawString("🛡 " + armorValue + " / 20", 16, 54);
        }

        if (Modules.HUNGER_SYSTEM) {
            int hungerW = 200;
            int hungerX = 12;
            int hungerY = armorValue > 0 ? 64 : 40;
            g.setColor(new Color(0, 0, 0, 180));
            g.fillRect(hungerX - 1, hungerY - 1, hungerW + 2, 12);
            g.setColor(new Color(90, 60, 30));
            g.fillRect(hungerX, hungerY, hungerW, 10);
            g.setColor(new Color(200, 130, 50));
            int hFill = (int) (hungerW * (player.hunger / player.maxHunger));
            g.fillRect(hungerX, hungerY, hFill, 10);
            g.setColor(new Color(255, 200, 100));
            g.setFont(PixelFont.font(9, Font.BOLD));
            g.drawString("Еда: " + (int) player.hunger, hungerX + 4, hungerY + 9);
        }

        int xpBarW = 300;
        int xpBarX = (SCREEN_W - xpBarW) / 2;
        int xpBarY = SCREEN_H - SLOT - 30;
        g.setColor(new Color(0, 0, 0));
        g.fillRect(xpBarX - 2, xpBarY - 2, xpBarW + 4, 14);
        g.setColor(new Color(60, 30, 90));
        g.fillRect(xpBarX, xpBarY, xpBarW, 10);
        g.setColor(new Color(120, 60, 200));
        int xpFill = (int) (xpBarW * (xp / (double) xpToNext));
        g.fillRect(xpBarX, xpBarY, xpFill, 10);
        g.setColor(new Color(200, 140, 255));
        g.fillRect(xpBarX, xpBarY, xpFill, 3);

        g.setFont(PixelFont.font(13, Font.BOLD));
        g.setColor(new Color(0, 0, 0));
        g.drawString("Ур. " + xpLevel, xpBarX - 46, xpBarY + 10);
        g.setColor(new Color(200, 140, 255));
        g.drawString("Ур. " + xpLevel, xpBarX - 47, xpBarY + 9);

        String timeStr = isNight() ? "🌙 НОЧЬ" : "☀ ДЕНЬ";
        g.setFont(PixelFont.font(13, Font.BOLD));
        g.setColor(new Color(0, 0, 0));
        g.drawString(timeStr, SCREEN_W - 95, 27);
        g.setColor(isNight() ? new Color(180, 180, 255) : new Color(255, 240, 100));
        g.drawString(timeStr, SCREEN_W - 96, 26);

        if (weather != Weather.CLEAR) {
            String wname = "";
            switch (weather) {
                case RAIN:
                    wname = "🌧 Дождь";
                    break;
                case SNOW:
                    wname = "❄ Снег";
                    break;
                case STORM:
                    wname = "⛈ Гроза";
                    break;
                case SANDSTORM:
                    wname = "🌪 Буря";
                    break;
            }
            g.setColor(new Color(150, 200, 255));
            g.drawString(wname, SCREEN_W - 105, 47);
        }

        if (mode == GameMode.CREATIVE) {
            g.setColor(new Color(0, 0, 0));
            g.drawString("КРЕАТИВ", SCREEN_W - 82, 67);
            g.setColor(new Color(100, 240, 240));
            g.drawString("КРЕАТИВ", SCREEN_W - 83, 66);
        } else if (mode == GameMode.HARDCORE) {
            g.setColor(new Color(0, 0, 0));
            g.drawString("ХАРДКОР", SCREEN_W - 82, 67);
            g.setColor(new Color(255, 100, 100));
            g.drawString("ХАРДКОР", SCREEN_W - 83, 66);
        }

        if (mp != null) {
            g.setColor(new Color(0, 0, 0));
            g.drawString(mp.isHost() ? "ХОСТ" : "КЛИЕНТ", SCREEN_W - 82, 87);
            g.setColor(new Color(120, 240, 120));
            g.drawString(mp.isHost() ? "ХОСТ" : "КЛИЕНТ", SCREEN_W - 83, 86);
        }

        int gold = countItem(World.COIN_GOLD);
        if (gold > 0) {
            g.setFont(PixelFont.font(13, Font.BOLD));
            g.setColor(new Color(0, 0, 0));
            g.drawString("★ " + gold, 12, SCREEN_H - 12);
            g.setColor(new Color(255, 220, 80));
            g.drawString("★ " + gold, 11, SCREEN_H - 13);
        }

        if (showFPS) {
            g.setFont(PixelFont.font(11, Font.BOLD));
            g.setColor(new Color(0, 0, 0));
            g.drawString(fps + " FPS", 12, SCREEN_H - 30);
            g.setColor(new Color(180, 255, 180));
            g.drawString(fps + " FPS", 11, SCREEN_H - 31);
        }

        if (showCoordinates) {
            g.setFont(PixelFont.font(11, Font.BOLD));
            g.setColor(new Color(0, 0, 0));
            g.drawString("X:" + (int) (player.x / TILE) + " Y:" + (int) (player.y / TILE), 12, SCREEN_H - 48);
            g.setColor(new Color(200, 220, 255));
            g.drawString("X:" + (int) (player.x / TILE) + " Y:" + (int) (player.y / TILE), 11, SCREEN_H - 49);
        }

        int totalW = INV_COLS * SLOT;
        int startX = (SCREEN_W - totalW) / 2;
        int startY = SCREEN_H - SLOT - 10;

        g.setColor(new Color(0, 0, 0, 180));
        g.fillRect(startX - 4, startY - 4, totalW + 8, SLOT + 8);
        g.setColor(new Color(140, 140, 140));
        g.drawRect(startX - 4, startY - 4, totalW + 8, SLOT + 8);

        for (int i = 0; i < INV_COLS; i++) {
            int sx = startX + i * SLOT;
            boolean sel = i == selectedSlot;
            drawMinecraftSlot(g, sx, startY, sel);
            if (inventory[i] != null) {
                drawSlotItem(g, inventory[i], sx, startY);
            }
        }
    }

    private void drawPixelHeart(Graphics2D g, int x, int y, double fill) {
        int px = 2;
        int[][] heart = {
            {0, 1, 1, 0, 1, 1, 0},
            {1, 1, 1, 1, 1, 1, 1},
            {1, 1, 1, 1, 1, 1, 1},
            {0, 1, 1, 1, 1, 1, 0},
            {0, 0, 1, 1, 1, 0, 0},
            {0, 0, 0, 1, 0, 0, 0}
        };
        for (int row = 0; row < heart.length; row++) {
            for (int col = 0; col < heart[row].length; col++) {
                if (heart[row][col] == 1) {
                    g.setColor(new Color(30, 0, 0));
                    g.fillRect(x + col * px, y + row * px, px, px);
                }
            }
        }
        if (fill > 0) {
            int filledCols = (int) Math.ceil(heart[0].length * fill);
            for (int row = 0; row < heart.length; row++) {
                for (int col = 0; col < heart[row].length; col++) {
                    if (heart[row][col] == 1 && col < filledCols) {
                        int shade = row < 2 ? 220 : 180;
                        g.setColor(new Color(shade, 20, 20));
                        g.fillRect(x + col * px, y + row * px, px, px);
                    }
                }
            }
            g.setColor(new Color(255, 180, 180));
            g.fillRect(x + 2 * px, y + 1 * px, px, px);
        }
    }

    // ==================== ИНВЕНТАРЬ ====================
    private void drawInventory(Graphics2D g) {
        int totalW = INV_COLS * SLOT;
        int totalH = INV_ROWS * SLOT;
        int startX = (SCREEN_W - totalW) / 2 - 100;
        int startY = (SCREEN_H - totalH) / 2;

        int armorPanelW = 3 * SLOT + 30;
        int craftPanelW = 3 * SLOT + 40;
        int panelX = startX - armorPanelW - 40;
        int panelY = startY - 55;
        int panelW = totalW + craftPanelW + armorPanelW + 280;
        int panelH = totalH + 75;
        drawPixelPanel(g, panelX, panelY, panelW, panelH);

        g.setFont(PixelFont.font(20, Font.BOLD));
        g.setColor(new Color(0, 0, 0));
        g.drawString("ИНВЕНТАРЬ", startX + 2, startY - 30);
        g.setColor(new Color(255, 220, 100));
        g.drawString("ИНВЕНТАРЬ", startX, startY - 32);

        int armorX = startX - armorPanelW - 20;
        int armorY = startY;
        g.setFont(PixelFont.font(14, Font.BOLD));
        g.setColor(new Color(0, 0, 0));
        g.drawString("БРОНЯ", armorX + 2, armorY - 10);
        g.setColor(new Color(200, 220, 240));
        g.drawString("БРОНЯ", armorX, armorY - 12);

        String[] armorNames = {"Шлем", "Нагрудник", "Штаны", "Ботинки"};
        for (int i = 0; i < ARMOR_SLOTS; i++) {
            int sx = armorX;
            int sy = armorY + i * SLOT;
            drawMinecraftSlot(g, sx, sy, false);
            if (armorSlots[i] != null) {
                drawSlotItem(g, armorSlots[i], sx, sy);
            } else {
                g.setFont(PixelFont.font(9, Font.PLAIN));
                g.setColor(new Color(150, 150, 170));
                g.drawString(armorNames[i], sx + 4, sy + SLOT - 6);
            }
        }

        int armorPoints = player.getArmorPoints();
        g.setFont(PixelFont.font(14, Font.BOLD));
        g.setColor(new Color(200, 220, 240));
        g.drawString("Защита: " + armorPoints, armorX, armorY + ARMOR_SLOTS * SLOT + 20);

        for (int r = 0; r < INV_ROWS; r++) {
            for (int c = 0; c < INV_COLS; c++) {
                int i = r * INV_COLS + c;
                int sx = startX + c * SLOT;
                int sy = startY + r * SLOT;
                drawMinecraftSlot(g, sx, sy, i == selectedSlot);
                if (inventory[i] != null && i != draggedFromSlot) {
                    drawSlotItem(g, inventory[i], sx, sy);
                }
            }
        }

        int craftX = startX + totalW + 40;
        int craftY = startY;

        g.setFont(PixelFont.font(16, Font.BOLD));
        g.setColor(new Color(0, 0, 0));
        g.drawString("КРАФТ", craftX + 2, craftY - 10);
        g.setColor(new Color(255, 220, 100));
        g.drawString("КРАФТ", craftX, craftY - 12);

        for (int r = 0; r < 3; r++) {
            for (int c = 0; c < 3; c++) {
                int i = r * 3 + c;
                int sx = craftX + c * SLOT;
                int sy = craftY + r * SLOT;
                drawMinecraftSlot(g, sx, sy, false);
                if (craftGrid[i] != null) {
                    drawSlotItem(g, craftGrid[i], sx, sy);
                }
            }
        }

        int arrowX = craftX + 3 * SLOT + 15;
        int arrowY = craftY + SLOT + 10;
        g.setColor(new Color(200, 200, 220));
        g.fillRect(arrowX, arrowY, 30, 4);
        Polygon p = new Polygon();
        p.addPoint(arrowX + 30, arrowY - 12);
        p.addPoint(arrowX + 30, arrowY + 16);
        p.addPoint(arrowX + 42, arrowY + 2);
        g.fillPolygon(p);

        int resX = arrowX + 50;
        int resY = craftY + SLOT;
        drawMinecraftSlot(g, resX, resY, false);
        if (craftResult != null) {
            drawSlotItem(g, craftResult, resX, resY);
        }
        updateCraftResult();

        if (nearWorkbench) {
            g.setFont(PixelFont.font(11, Font.BOLD));
            g.setColor(new Color(120, 255, 120));
            g.drawString("✔ Рядом верстак", craftX, craftY + 3 * SLOT + 25);
        } else {
            g.setFont(PixelFont.font(11, Font.PLAIN));
            g.setColor(new Color(180, 180, 200));
            g.drawString("Нужен верстак для полного крафта", craftX, craftY + 3 * SLOT + 25);
        }

        g.setFont(PixelFont.font(11, Font.PLAIN));
        g.setColor(new Color(180, 200, 240));
        String hint = "ЛКМ — взять/положить  ·  ПКМ — половина стака  ·  Shift+ЛКМ — быстрый перенос";
        g.drawString(hint, panelX + 20, panelY + panelH - 8);
    }

    private void drawSlotItem(Graphics2D g, ItemStack stack, int sx, int sy) {
        BufferedImage icon = Textures.get(stack.id);
        g.drawImage(icon, sx + 8, sy + 8, SLOT - 18, SLOT - 18, null);
        if (stack.count > 1) {
            g.setFont(PixelFont.font(13, Font.BOLD));
            g.setColor(new Color(0, 0, 0));
            g.drawString("" + stack.count, sx + SLOT - 20, sy + SLOT - 6);
            g.setColor(Color.WHITE);
            g.drawString("" + stack.count, sx + SLOT - 21, sy + SLOT - 7);
        }
        if (stack.durability > 0 && stack.maxDurability > 0 && stack.durability < stack.maxDurability) {
            int barW = SLOT - 10;
            int barX = sx + 5;
            int barY = sy + SLOT - 10;
            g.setColor(new Color(0, 0, 0, 200));
            g.fillRect(barX, barY, barW, 3);
            double ratio = stack.durability / (double) stack.maxDurability;
            Color c = ratio > 0.5 ? new Color(80, 220, 80)
                    : ratio > 0.2 ? new Color(240, 200, 60)
                            : new Color(240, 60, 60);
            g.setColor(c);
            g.fillRect(barX, barY, (int) (barW * ratio), 3);
        }
    }

    private void updateCraftResult() {
        currentRecipe = Crafting.findRecipe(craftGrid, nearWorkbench);
        if (currentRecipe != null) {
            craftResult = ItemStack.of(currentRecipe.resultId, currentRecipe.resultCount);
        } else {
            craftResult = null;
        }
    }

    // ==================== КОНТЕЙНЕРЫ ====================
    private void drawContainer(Graphics2D g) {
        if (containerSlots == null) {
            return;
        }
        boolean isFurnace = activeContainer.type == World.FURNACE;
        int cols = activeContainer.type == World.CHEST ? 9 : 3;
        int rows = 3;
        int totalW = cols * SLOT;
        int totalH = rows * SLOT;
        int startX = (SCREEN_W - totalW) / 2;
        int startY = (SCREEN_H - totalH) / 2 - 200;
        drawPixelPanel(g, startX - 20, startY - 55, totalW + 40, totalH + 75);

        g.setFont(PixelFont.font(20, Font.BOLD));
        String title = activeContainer.type == World.CHEST ? "СУНДУК"
                : isFurnace ? "ПЕЧЬ" : "ВЕРСТАК";
        g.setColor(new Color(0, 0, 0));
        g.drawString(title, startX + 2, startY - 30);
        g.setColor(new Color(255, 220, 100));
        g.drawString(title, startX, startY - 32);

        for (int r = 0; r < rows; r++) {
            for (int c = 0; c < cols; c++) {
                int i = r * cols + c;
                int sx = startX + c * SLOT;
                int sy = startY + r * SLOT;
                drawMinecraftSlot(g, sx, sy, false);
                if (containerSlots[i] != null) {
                    drawSlotItem(g, containerSlots[i], sx, sy);
                }
                if (isFurnace) {
                    g.setColor(new Color(180, 180, 220));
                    g.setFont(PixelFont.font(10, Font.PLAIN));
                    if (i == 0) {
                        g.drawString("РУДА", sx + 8, sy + 14);
                    }
                    if (i == 1) {
                        g.drawString("ТОПЛ", sx + 8, sy + 14);
                    }
                    if (i == 2) {
                        g.drawString("ТОПЛ", sx + 8, sy + 14);
                    }
                    if (i == 8) {
                        g.drawString("РЕЗ.", sx + 10, sy + 14);
                    }
                }
            }
        }

        if (isFurnace && activeContainer.cookTime > 0) {
            int barX = startX + totalW + 30;
            int barY = startY;
            int barW = 30;
            int barH = totalH;
            g.setColor(new Color(20, 15, 10));
            g.fillRect(barX - 2, barY - 2, barW + 4, barH + 4);
            g.setColor(new Color(120, 80, 45));
            g.drawRect(barX - 2, barY - 2, barW + 4, barH + 4);
            double progress = 1.0 - (activeContainer.cookTime / (double) WorkBlock.COOK_TIME);
            int fillH = (int) (barH * progress);
            g.setColor(new Color(255, 140, 40));
            g.fillRect(barX + 2, barY + barH - fillH - 2, barW - 4, fillH);
            g.setColor(new Color(255, 220, 100));
            g.fillRect(barX + 2, barY + barH - fillH - 2, barW - 4, 4);
        }
    }

    // ==================== ЧАТ ====================
    private void drawChat(Graphics2D g) {
        int startY = SCREEN_H - SLOT - 60;
        g.setFont(PixelFont.font(13, Font.PLAIN));
        int count = Math.min(chatVisibleCount, chatLog.size());
        for (int i = 0; i < count; i++) {
            ChatMessage msg = chatLog.get(chatLog.size() - count + i);
            int y = startY - (count - i) * 20;
            long age = System.currentTimeMillis() - msg.time;
            float alpha = age > 8000 ? Math.max(0.2f, (12000 - age) / 4000f) : 1f;
            g.setColor(new Color(0, 0, 0, (int) (140 * alpha)));
            FontMetrics fm = g.getFontMetrics();
            g.fillRect(10, y - 14, fm.stringWidth(msg.text) + 14, 20);
            g.setColor(new Color(msg.color.getRed(), msg.color.getGreen(),
                    msg.color.getBlue(), (int) (255 * alpha)));
            g.drawString(msg.text, 17, y);
        }

        if (chatOpen) {
            g.setColor(new Color(0, 0, 0, 220));
            g.fillRect(10, startY, SCREEN_W - 20, 32);
            g.setColor(new Color(255, 255, 255));
            g.drawRect(10, startY, SCREEN_W - 20, 32);

            String[] channels = {"[ВСЕ]", "[ЛОК]", "[СИС]"};
            Color chColor = chatChannel == 0 ? Color.WHITE
                    : chatChannel == 1 ? new Color(200, 240, 200)
                            : new Color(240, 200, 200);
            g.setColor(chColor);
            g.setFont(PixelFont.font(14, Font.BOLD));
            g.drawString(channels[chatChannel], 18, startY + 22);

            g.setColor(Color.WHITE);
            g.drawString("> " + chatInput + "_", 90, startY + 22);
        }
    }

    // ==================== ПАУЗА / СМЕРТЬ ====================
    private void drawPause(Graphics2D g) {
        g.setColor(new Color(0, 0, 0, 200));
        g.fillRect(0, 0, SCREEN_W, SCREEN_H);
        g.setFont(PixelFont.font(58, Font.BOLD));
        drawCenteredWithPixelShadow(g, "ПАУЗА", SCREEN_W / 2, SCREEN_H / 2 - 140, new Color(255, 220, 100));

        drawMCButton(g, "Продолжить [Esc]", SCREEN_W / 2 - 200, SCREEN_H / 2 - 60, 400, 55,
                mouseY > SCREEN_H / 2 - 60 && mouseY < SCREEN_H / 2 - 5 && mouseX > SCREEN_W / 2 - 200 && mouseX < SCREEN_W / 2 + 200);
        drawMCButton(g, "Сохранить [S]", SCREEN_W / 2 - 200, SCREEN_H / 2 + 10, 400, 55,
                mouseY > SCREEN_H / 2 + 10 && mouseY < SCREEN_H / 2 + 65 && mouseX > SCREEN_W / 2 - 200 && mouseX < SCREEN_W / 2 + 200);
        drawMCButton(g, "Настройки", SCREEN_W / 2 - 200, SCREEN_H / 2 + 80, 400, 55,
                mouseY > SCREEN_H / 2 + 80 && mouseY < SCREEN_H / 2 + 135 && mouseX > SCREEN_W / 2 - 200 && mouseX < SCREEN_W / 2 + 200);
        drawMCButton(g, "В меню [Q]", SCREEN_W / 2 - 200, SCREEN_H / 2 + 150, 400, 55,
                mouseY > SCREEN_H / 2 + 150 && mouseY < SCREEN_H / 2 + 205 && mouseX > SCREEN_W / 2 - 200 && mouseX < SCREEN_W / 2 + 200);
    }

    private void drawDeath(Graphics2D g) {
        g.setColor(new Color(100, 0, 0, 210));
        g.fillRect(0, 0, SCREEN_W, SCREEN_H);
        g.setFont(PixelFont.font(58, Font.BOLD));
        drawCenteredWithPixelShadow(g, "ТЫ УМЕР", SCREEN_W / 2, SCREEN_H / 2 - 60, new Color(255, 100, 100));
        g.setFont(PixelFont.font(18, Font.PLAIN));
        g.setColor(Color.WHITE);
        drawCentered(g, "[ R ] Возродиться    [ Q ] В меню", SCREEN_W / 2, SCREEN_H / 2 + 30);
        if (mode == GameMode.HARDCORE) {
            g.setFont(PixelFont.font(16, Font.BOLD));
            g.setColor(new Color(255, 200, 100));
            drawCentered(g, "ХАРДКОР: мир удалён!", SCREEN_W / 2, SCREEN_H / 2 + 70);
        }
    }

    // ==================== ТОРГОВЛЯ ====================
    private void drawTrade(Graphics2D g) {
        g.setColor(new Color(0, 0, 0, 220));
        g.fillRect(0, 0, SCREEN_W, SCREEN_H);

        int panelW = 720, panelH = 500;
        int px = (SCREEN_W - panelW) / 2;
        int py = (SCREEN_H - panelH) / 2;
        drawPixelPanel(g, px, py, panelW, panelH);

        g.setFont(PixelFont.font(24, Font.BOLD));
        g.setColor(new Color(0, 0, 0));
        g.drawString("ТОРГОВЛЯ", px + 32, py + 42);
        g.setColor(new Color(255, 220, 100));
        g.drawString("ТОРГОВЛЯ", px + 30, py + 40);

        int gold = countItem(World.COIN_GOLD);
        g.setFont(PixelFont.font(16, Font.BOLD));
        g.setColor(new Color(255, 220, 80));
        g.drawString("★ Ваше золото: " + gold, px + panelW - 240, py + 40);

        g.setColor(new Color(120, 90, 60));
        g.fillRect(px + 20, py + 60, panelW - 40, 2);

        g.setFont(PixelFont.font(14, Font.BOLD));
        g.setColor(new Color(200, 220, 255));
        g.drawString("Ур. жителя: " + tradingVillager.level, px + 30, py + 90);
        g.drawString("Опыт: " + tradingVillager.xp + " / " + (tradingVillager.level * 5), px + 200, py + 90);

        List<TradeRecipe> recipes = tradingVillager.getRecipes();
        int rows = Math.min(7, recipes.size());
        for (int i = 0; i < rows; i++) {
            int idx = i + tradeScroll;
            if (idx >= recipes.size()) {
                break;
            }
            TradeRecipe r = recipes.get(idx);
            int ry = py + 120 + i * 50;
            boolean canAfford = gold >= r.priceGold;

            boolean hover = mouseY > ry && mouseY < ry + 42 && mouseX > px + 20 && mouseX < px + panelW - 20;
            g.setColor(hover ? new Color(90, 70, 50) : new Color(55, 45, 30));
            g.fillRect(px + 20, ry, panelW - 40, 42);
            g.setColor(canAfford ? new Color(180, 140, 80) : new Color(120, 60, 60));
            g.drawRect(px + 20, ry, panelW - 40, 42);

            g.drawImage(Textures.get(r.itemId), px + 40, ry + 5, 32, 32, null);
            g.setFont(PixelFont.font(14, Font.BOLD));
            g.setColor(canAfford ? Color.WHITE : new Color(255, 150, 150));
            g.drawString("×" + r.count, px + 78, ry + 28);

            g.setColor(new Color(200, 220, 255));
            g.setFont(PixelFont.font(13, Font.PLAIN));
            g.drawString(World.blockName(r.itemId), px + 130, ry + 27);

            g.setFont(PixelFont.font(15, Font.BOLD));
            g.setColor(canAfford ? new Color(255, 220, 80) : new Color(150, 100, 50));
            g.drawString("★ " + r.priceGold, px + panelW - 180, ry + 28);

            int bx = px + panelW - 90;
            int by = ry + 8;
            g.setColor(canAfford ? new Color(60, 140, 60) : new Color(60, 60, 60));
            g.fillRect(bx, by, 70, 26);
            g.setColor(canAfford ? new Color(120, 220, 120) : new Color(100, 100, 100));
            g.drawRect(bx, by, 70, 26);
            g.setColor(Color.WHITE);
            g.setFont(PixelFont.font(12, Font.BOLD));
            g.drawString("КУПИТЬ", bx + 8, by + 18);
        }

        g.setFont(PixelFont.font(12, Font.PLAIN));
        g.setColor(new Color(200, 200, 200));
        g.drawString("[ ↑/↓ ] Навигация   [ Enter ] Купить   [ Esc ] Выйти", px + 30, py + panelH - 20);
    }
    // ==================== ЛОГИКА: КОПАНИЕ ====================

    private void startDigging(int wx, int wy) {
        int block = world.getBlock(wx, wy);
        if (block == World.AIR) {
            return;
        }

        double pdx = wx * TILE - player.x;
        double pdy = wy * TILE - player.y;
        if (pdx * pdx + pdy * pdy > (6 * TILE) * (6 * TILE)) {
            return;
        }

        if (block == World.CHEST || block == World.FURNACE
                || block == World.WORKBENCH || block == World.CRAFT_TABLE) {
            return;
        }
        if (block == World.DOOR_CLOSED || block == World.DOOR_OPEN) {
            return;
        }

        ItemStack held = inventory[selectedSlot];

        // === ПРОВЕРКА: нужен ли инструмент ===
        if (ToolUtil.requiresTool(block) && !ToolUtil.canHarvest(held, block)) {
            String toolName = ToolUtil.getRequiredTool(block);
            notify("Нужен " + toolName + "!", new Color(255, 100, 100));
            Sound.play(Sound.HIT);
            digX = -1;
            digProgress = 0;
            return;
        }

        digX = wx;
        digY = wy;
        digProgress = 0;

        int hardness = ToolUtil.getBlockHardness(block);
        int toolPower = ToolUtil.getToolPower(held);
        int toolBonus = ToolUtil.getToolBonus(held, block);

        int baseTicks = hardness * 10;
        int power = toolPower + toolBonus;
        if (power < 1) {
            power = 1;
        }
        digRequired = Math.max(3, baseTicks / power);
        if (ToolUtil.isWrongTool(held, block)) {
            digRequired *= 3;
        }

        // Кулаком по мягким блокам — медленнее
        if (held == null && !ToolUtil.requiresTool(block)) {
            digRequired *= 2;
        }

        if (Modules.TOOLS_WEAR && held != null && ToolUtil.isTool(held.id)) {
            held.damage(1);
            if (held.durability <= 0) {
                inventory[selectedSlot] = null;
                Sound.play(Sound.HIT);
                notify("Инструмент сломан!", new Color(255, 100, 100));
            }
        }
    }

    private void continueDigging() {
        int block = world.getBlock(digX, digY);
        if (block == World.AIR) {
            digX = -1;
            digProgress = 0;
            return;
        }

        digProgress++;
        if (digProgress >= digRequired) {
            world.setBlock(digX, digY, World.AIR);

            if (mode == GameMode.SURVIVAL || mode == GameMode.HARDCORE) {
                if (block == World.GOLD) {
                    addToInventory(ItemStack.of(World.COIN_GOLD, 3));
                } else if (block == World.DIAMOND) {
                    addToInventory(ItemStack.of(World.COIN_GOLD, 5));
                } else if (block == World.IRON) {
                    addToInventory(ItemStack.of(World.COIN_GOLD, 1));
                }

                addToInventory(ItemStack.of(block, 1));
                addXp(1);
                unlock("first_block");

                if (block == World.WOOD && countItem(World.WOOD) >= 10) {
                    unlock("wood");
                }
                if (block == World.IRON) {
                    unlock("iron");
                }
                if (block == World.GOLD) {
                    unlock("gold");
                }
                if (block == World.DIAMOND) {
                    unlock("diamond");
                }
            }

            if (mp != null) {
                mp.sendBlockChange(digX, digY, World.AIR);
            }
            Sound.play(Sound.MINE);

            for (int i = 0; i < 5; i++) {
                floaters.add(new FloatingText("•", digX * TILE + new Random().nextInt(TILE),
                        digY * TILE + new Random().nextInt(TILE), new Color(200, 200, 200)));
            }

            digX = -1;
            digProgress = 0;
        }
    }

    // ==================== ЛОГИКА: КЛИКИ ====================
    private void handleClick(MouseEvent e) {
        if (state == GameState.PLAYING && chatOpen) {
            return;
        }
        Sound.play(Sound.CLICK);

        switch (state) {
            case MENU:
                handleMenuClick();
                break;
            case WORLD_SELECT:
                handleWorldSelectClick();
                break;
            case WORLD_CREATE:
                handleWorldCreateClick();
                break;
            case MULTIPLAYER:
                handleMultiplayerClick();
                break;
            case PLAYING:
                handleGameClick(e);
                break;
            case PAUSED:
                handlePauseClick();
                break;
            case ACHIEVEMENTS:
                if (mouseY > SCREEN_H - 60 && mouseY < SCREEN_H - 15) {
                    state = GameState.MENU;
                }
                break;
            case SETTINGS:
                handleSettingsClick();
                break;
            case RESOURCEPACKS:
                handleResourcePacksClick();
                break;
            case TRADE:
                handleTradeClick();
                break;
            case MP_HOST_WAITING:
                handleMpHostWaitingClick();
                break;
        }
    }

    private void handleMenuClick() {
        int bx = SCREEN_W / 2 - 200;
        if (mouseX < bx || mouseX > bx + 400) {
            return;
        }
        int startY = 240;
        for (int i = 0; i < 4; i++) {
            int y = startY + i * 55;
            if (mouseY > y && mouseY < y + 42) {
                switch (i) {
                    case 0:
                        state = GameState.WORLD_SELECT;
                        break;
                    case 1:
                        state = GameState.MULTIPLAYER;
                        break;
                    case 2:
                        state = GameState.SETTINGS;
                        settingsTab = 0;
                        break;
                    case 3:
                        System.exit(0);
                        break;
                }
                return;
            }
        }
    }

    private void handleWorldSelectClick() {
        int listX = 60, listY = 110, itemH = 70, listW = 520;
        for (int i = 0; i < Math.min(worldSaves.size(), 6); i++) {
            int y = listY + i * itemH;
            if (mouseY > y && mouseY < y + itemH - 6 && mouseX > listX && mouseX < listX + listW) {
                selectedWorldIndex = i;
                loadSelectedWorld();
                return;
            }
        }
        if (mouseY > 540 && mouseY < 590) {
            if (mouseX > 60 && mouseX < 310) {
                state = GameState.WORLD_CREATE;
                inputSeed = "";
                typingSeed = true;
                worldSettingsTab = 0;
                return;
            }
            if (mouseX > 330 && mouseX < 580 && !worldSaves.isEmpty()) {
                loadSelectedWorld();
                return;
            }
        }
        if (mouseY > 600 && mouseY < 650) {
            if (mouseX > 60 && mouseX < 260) {
                state = GameState.MENU;
                return;
            }
            if (mouseX > 330 && mouseX < 580 && !worldSaves.isEmpty()) {
                deleteWorld();
                return;
            }
        }
    }

    private void handleWorldCreateClick() {
        if (mouseY > 130 && mouseY < 170 && mouseX > SCREEN_W / 2 - 250 && mouseX < SCREEN_W / 2 + 250) {
            typingSeed = true;
            return;
        }
        typingSeed = false;

        String[] tabs = {"Размер", "Тип", "Сложность", "Ресурсы"};
        int tabW = 130;
        int tabX = SCREEN_W / 2 - (tabs.length * tabW) / 2;
        int tabY = 200;
        for (int i = 0; i < tabs.length; i++) {
            int tx = tabX + i * tabW;
            if (mouseY > tabY && mouseY < tabY + 40 && mouseX > tx && mouseX < tx + tabW - 6) {
                worldSettingsTab = i;
                return;
            }
        }

        int contX = SCREEN_W / 2 - 300;
        int contY = 260;

        if (worldSettingsTab == 0) {
            if (mouseY > contY + 90 && mouseY < contY + 125) {
                if (mouseX > contX + 20 && mouseX < contX + 90) {
                    newWorldWidth = Math.max(200, newWorldWidth - 100);
                    return;
                }
                if (mouseX > contX + 100 && mouseX < contX + 170) {
                    newWorldWidth = Math.min(2000, newWorldWidth + 100);
                    return;
                }
            }
            if (mouseY > contY + 190 && mouseY < contY + 225) {
                if (mouseX > contX + 20 && mouseX < contX + 90) {
                    newWorldHeight = Math.max(100, newWorldHeight - 100);
                    return;
                }
                if (mouseX > contX + 100 && mouseX < contX + 170) {
                    newWorldHeight = Math.min(400, newWorldHeight + 100);
                    return;
                }
            }
        } else if (worldSettingsTab == 1) {
            WorldType[] types = WorldType.values();
            int cols = 3, btnW = 170, btnH = 45, gap = 15;
            for (int i = 0; i < types.length; i++) {
                int cx = contX + 20 + (i % cols) * (btnW + gap);
                int cy = contY + 50 + (i / cols) * (btnH + gap);
                if (mouseY > cy && mouseY < cy + btnH && mouseX > cx && mouseX < cx + btnW) {
                    newWorldType = types[i];
                    return;
                }
            }
        } else if (worldSettingsTab == 2) {
            GameMode[] modes = GameMode.values();
            for (int i = 0; i < modes.length; i++) {
                int cx = contX + 20 + i * 190;
                int cy = contY + 50;
                if (mouseY > cy && mouseY < cy + 45 && mouseX > cx && mouseX < cx + 170) {
                    newWorldMode = modes[i];
                    return;
                }
            }
            Difficulty[] diffs = Difficulty.values();
            for (int i = 0; i < diffs.length; i++) {
                int cx = contX + 20 + i * 145;
                int cy = contY + 160;
                if (mouseY > cy && mouseY < cy + 45 && mouseX > cx && mouseX < cx + 135) {
                    newWorldDifficulty = diffs[i];
                    return;
                }
            }
        } else if (worldSettingsTab == 3) {
            if (mouseY > contY + 25 && mouseY < contY + 45 && mouseX > contX + 300 && mouseX < contX + 560) {
                newWorldOreDensity = (mouseX - (contX + 300)) / 260.0 * 3.0;
                return;
            }
            if (mouseY > contY + 75 && mouseY < contY + 95 && mouseX > contX + 300 && mouseX < contX + 560) {
                newWorldTreeDensity = (mouseX - (contX + 300)) / 260.0 * 3.0;
                return;
            }
            if (mouseY > contY + 125 && mouseY < contY + 145 && mouseX > contX + 300 && mouseX < contX + 560) {
                newWorldMonsterRate = (mouseX - (contX + 300)) / 260.0 * 3.0;
                return;
            }
            if (mouseY > contY + 175 && mouseY < contY + 210 && mouseX > contX + 400 && mouseX < contX + 560) {
                newWorldStructures = !newWorldStructures;
                return;
            }
        }

        if (mouseY > SCREEN_H - 90 && mouseY < SCREEN_H - 35
                && mouseX > SCREEN_W / 2 - 220 && mouseX < SCREEN_W / 2 + 220) {
            createWorldWithSettings();
            return;
        }
        if (mouseY > SCREEN_H - 30 && mouseY < SCREEN_H - 5
                && mouseX > SCREEN_W / 2 - 150 && mouseX < SCREEN_W / 2 + 150) {
            state = GameState.WORLD_SELECT;
        }
    }

    private void handleMultiplayerClick() {
        if (mouseY > 165 && mouseY < 205 && mouseX > SCREEN_W / 2 - 250 && mouseX < SCREEN_W / 2 + 250) {
            typingMpAddress = true;
            return;
        }
        typingMpAddress = false;
        if (mouseY > 250 && mouseY < 305 && mouseX > SCREEN_W / 2 - 220 && mouseX < SCREEN_W / 2 + 220) {
            startMultiplayerHost();
            return;
        }
        if (mouseY > 320 && mouseY < 375 && mouseX > SCREEN_W / 2 - 220 && mouseX < SCREEN_W / 2 + 220) {
            startMultiplayerClient();
            return;
        }
        if (mouseY > SCREEN_H - 70 && mouseY < SCREEN_H - 20
                && mouseX > SCREEN_W / 2 - 150 && mouseX < SCREEN_W / 2 + 150) {
            state = GameState.MENU;
        }
    }

    private void handleMpHostWaitingClick() {
        if (mouseY > SCREEN_H - 120 && mouseY < SCREEN_H - 65
                && mouseX > SCREEN_W / 2 - 220 && mouseX < SCREEN_W / 2 + 220) {
            if (mp != null) {
                mp.startGameAsHost();
            }
            return;
        }
        if (mouseY > SCREEN_H - 55 && mouseY < SCREEN_H - 10
                && mouseX > SCREEN_W / 2 - 150 && mouseX < SCREEN_W / 2 + 150) {
            if (mp != null) {
                mp.close();
                mp = null;
            }
            state = GameState.MULTIPLAYER;
        }
    }

    private void handlePauseClick() {
        if (mouseX < SCREEN_W / 2 - 200 || mouseX > SCREEN_W / 2 + 200) {
            return;
        }
        if (mouseY > SCREEN_H / 2 - 60 && mouseY < SCREEN_H / 2 - 5) {
            state = GameState.PLAYING;
        } else if (mouseY > SCREEN_H / 2 + 10 && mouseY < SCREEN_H / 2 + 65) {
            saveCurrentWorld();
        } else if (mouseY > SCREEN_H / 2 + 80 && mouseY < SCREEN_H / 2 + 135) {
            state = GameState.SETTINGS;
        } else if (mouseY > SCREEN_H / 2 + 150 && mouseY < SCREEN_H / 2 + 205) {
            backToMenu();
        }
    }

    private void handleSettingsClick() {
        String[] tabs = {"Игра", "Звук", "Прочее"};
        int tabW = 200;
        int tabX = SCREEN_W / 2 - (tabs.length * tabW) / 2;
        int tabY = 80;
        for (int i = 0; i < tabs.length; i++) {
            int tx = tabX + i * tabW;
            if (mouseY > tabY && mouseY < tabY + 42 && mouseX > tx && mouseX < tx + tabW - 6) {
                settingsTab = i;
                return;
            }
        }

        int cx = 100, cy = 140;

        if (mouseY > SCREEN_H - 60 && mouseY < SCREEN_H - 15) {
            if (mouseX > SCREEN_W / 2 - 320 && mouseX < SCREEN_W / 2 - 20) {
                saveSettings();
                notify("Настройки сохранены", new Color(120, 255, 120));
                return;
            }
            if (mouseX > SCREEN_W / 2 + 20 && mouseX < SCREEN_W / 2 + 320) {
                state = GameState.MENU;
                return;
            }
        }

        if (settingsTab == 0) {
            if (mouseY > cy + 70 && mouseY < cy + 102 && mouseX > cx + 300 && mouseX < cx + 440) {
                showFPS = !showFPS;
                return;
            }
            if (mouseY > cy + 120 && mouseY < cy + 152 && mouseX > cx + 300 && mouseX < cx + 440) {
                showCoordinates = !showCoordinates;
                return;
            }
            if (mouseY > cy + 170 && mouseY < cy + 202 && mouseX > cx + 300 && mouseX < cx + 440) {
                autoSave = !autoSave;
                return;
            }
        } else if (settingsTab == 1) {
            if (mouseY > cy + 80 && mouseY < cy + 112) {
                if (mouseX > cx + 620 && mouseX < cx + 660) {
                    musicVolume = Math.max(0, musicVolume - 0.1f);
                    Music.setVolume(musicVolume);
                    return;
                }
                if (mouseX > cx + 670 && mouseX < cx + 710) {
                    musicVolume = Math.min(1, musicVolume + 0.1f);
                    Music.setVolume(musicVolume);
                    return;
                }
            }
            if (mouseY > cy + 140 && mouseY < cy + 172) {
                if (mouseX > cx + 620 && mouseX < cx + 660) {
                    sfxVolume = Math.max(0, sfxVolume - 0.1f);
                    Sound.setVolume(sfxVolume);
                    Sound.play(Sound.CLICK);
                    return;
                }
                if (mouseX > cx + 670 && mouseX < cx + 710) {
                    sfxVolume = Math.min(1, sfxVolume + 0.1f);
                    Sound.setVolume(sfxVolume);
                    Sound.play(Sound.CLICK);
                    return;
                }
            }
        }
    }

    private void handleResourcePacksClick() {
        int listY = 160, itemH = 60;
        for (int i = 0; i < Math.min(resourcePacks.size(), 5); i++) {
            int y = listY + i * itemH;
            if (mouseY > y && mouseY < y + itemH - 6 && mouseX > 80 && mouseX < SCREEN_W - 100) {
                selectedPackIndex = i;
                return;
            }
        }

        int btnY = 510;
        if (mouseY > btnY && mouseY < btnY + 42) {
            if (mouseX > 60 && mouseX < 240) {
                applyResourcePack(selectedPackIndex);
                return;
            }
            if (mouseX > 250 && mouseX < 430) {
                disableResourcePacks();
                return;
            }
            if (mouseX > 440 && mouseX < 670) {
                uploadResourcePack();
                return;
            }
            if (mouseX > 680 && mouseX < 880) {
                openResourcePacksFolder();
                return;
            }
            if (mouseX > 890 && mouseX < 1070) {
                refreshResourcePacks();
                notify("Ресурспаки обновлены", new Color(120, 255, 120));
                return;
            }
        }

        if (mouseY > SCREEN_H - 55 && mouseY < SCREEN_H - 10
                && mouseX > SCREEN_W / 2 - 150 && mouseX < SCREEN_W / 2 + 150) {
            state = GameState.MENU;
        }
    }

    private void uploadResourcePack() {
        new Thread(() -> {
            JFileChooser chooser = new JFileChooser();
            chooser.setDialogTitle("Выберите ресурспак (.zip)");
            chooser.setFileFilter(new FileNameExtensionFilter("Ресурспаки TerraPixel (*.zip)", "zip"));
            chooser.setAcceptAllFileFilterUsed(false);

            String home = System.getProperty("user.home");
            if (home != null) {
                chooser.setCurrentDirectory(new File(home + "/Downloads"));
            }

            int result = chooser.showOpenDialog(frame);
            if (result != JFileChooser.APPROVE_OPTION) {
                return;
            }

            File selected = chooser.getSelectedFile();
            if (selected == null || !selected.exists()) {
                return;
            }
            if (!selected.getName().toLowerCase().endsWith(".zip")) {
                SwingUtilities.invokeLater(() -> notify("Файл должен быть .zip", new Color(255, 100, 100)));
                return;
            }

            try {
                File dir = new File("resourcepacks");
                dir.mkdirs();
                File dest = new File(dir, selected.getName());
                if (dest.exists()) {
                    dest.delete();
                }

                try (InputStream in = new FileInputStream(selected); OutputStream out = new FileOutputStream(dest)) {
                    byte[] buf = new byte[8192];
                    int n;
                    while ((n = in.read(buf)) != -1) {
                        out.write(buf, 0, n);
                    }
                }

                SwingUtilities.invokeLater(() -> {
                    refreshResourcePacks();
                    for (int i = 0; i < resourcePacks.size(); i++) {
                        ResourcePack rp = resourcePacks.get(i);
                        if (rp.folder != null && rp.folder.getName().equals(selected.getName())) {
                            selectedPackIndex = i;
                            applyResourcePack(i);
                            notify("Ресурспак загружен: " + rp.name, new Color(120, 255, 120));
                            return;
                        }
                    }
                    notify("Ресурспак загружен", new Color(120, 255, 120));
                });
            } catch (Exception ex) {
                SwingUtilities.invokeLater(() -> notify("Ошибка загрузки: " + ex.getMessage(), new Color(255, 100, 100)));
            }
        }, "Upload-Pack").start();
    }

    private void applyResourcePack(int idx) {
        if (idx < 0 || idx >= resourcePacks.size()) {
            return;
        }
        ResourcePack rp = resourcePacks.get(idx);
        for (ResourcePack p : resourcePacks) {
            p.active = false;
        }
        rp.active = true;
        Textures.activePack = rp;
        Textures.reload();
        PixelFont.reload();
        notify("Применён: " + rp.name, new Color(120, 255, 120));
    }

    private void disableResourcePacks() {
        for (ResourcePack p : resourcePacks) {
            p.active = false;
        }
        Textures.activePack = null;
        Textures.reload();
        PixelFont.reload();
        notify("Возврат к default", new Color(200, 200, 200));
    }

    private void openResourcePacksFolder() {
        try {
            File dir = new File("resourcepacks");
            if (!dir.exists()) {
                dir.mkdirs();
            }
            java.awt.Desktop.getDesktop().open(dir);
        } catch (Exception ex) {
            notify("Не удалось открыть папку", new Color(255, 100, 100));
        }
    }

    private void handleTradeClick() {
        int panelW = 720, panelH = 500;
        int px = (SCREEN_W - panelW) / 2;
        int py = (SCREEN_H - panelH) / 2;

        List<TradeRecipe> recipes = tradingVillager.getRecipes();
        for (int i = 0; i < Math.min(7, recipes.size()); i++) {
            int idx = i + tradeScroll;
            if (idx >= recipes.size()) {
                break;
            }
            TradeRecipe r = recipes.get(idx);
            int ry = py + 120 + i * 50;
            if (mouseY > ry && mouseY < ry + 42 && mouseX > px + 20 && mouseX < px + panelW - 20) {
                doTrade(r);
                return;
            }
        }
    }

    // ==================== ЛОГИКА ИГРЫ ====================
    private void handleGameClick(MouseEvent e) {
        if (player == null) {
            return;
        }
        boolean isLeft = SwingUtilities.isLeftMouseButton(e);
        boolean isRight = SwingUtilities.isRightMouseButton(e);

        if (inventoryOpen && handleInventoryClick(mouseX, mouseY, isRight)) {
            return;
        }
        if (activeContainer != null && handleContainerClick(mouseX, mouseY, isRight)) {
            return;
        }

        int totalW = INV_COLS * SLOT;
        int startX = (SCREEN_W - totalW) / 2;
        int startY = SCREEN_H - SLOT - 10;
        if (mouseY >= startY && mouseY < startY + SLOT) {
            int idx = (mouseX - startX) / SLOT;
            if (idx >= 0 && idx < INV_COLS) {
                selectedSlot = idx;
                return;
            }
        }

        int wx = (int) ((mouseX + player.cameraX) / TILE);
        int wy = (int) ((mouseY + player.cameraY) / TILE);
        if (!world.inBounds(wx, wy)) {
            return;
        }

        double pdx = wx * TILE - player.x;
        double pdy = wy * TILE - player.y;
        if (pdx * pdx + pdy * pdy > (6 * TILE) * (6 * TILE)) {
            return;
        }

        if (isRight) {
            handleRightClick(wx, wy);
            return;
        }
        if (isLeft) {
            handleLeftClick(wx, wy);
        }
    }

    private void handleRightClick(int wx, int wy) {
        int clickedBlock = world.getBlock(wx, wy);

        if (clickedBlock == World.DOOR_CLOSED) {
            world.setBlock(wx, wy, World.DOOR_OPEN);
            if (mp != null) {
                mp.sendBlockChange(wx, wy, World.DOOR_OPEN);
            }
            Sound.play(Sound.CLICK);
            return;
        }
        if (clickedBlock == World.DOOR_OPEN) {
            world.setBlock(wx, wy, World.DOOR_CLOSED);
            if (mp != null) {
                mp.sendBlockChange(wx, wy, World.DOOR_CLOSED);
            }
            Sound.play(Sound.CLICK);
            return;
        }

        if (clickedBlock == World.CHEST || clickedBlock == World.FURNACE
                || clickedBlock == World.WORKBENCH || clickedBlock == World.CRAFT_TABLE) {
            openContainer(wx, wy, clickedBlock);
            Sound.play(Sound.CLICK);
            return;
        }

        for (Villager v : villagers) {
            if (Math.abs(v.x - wx * TILE) < TILE && Math.abs(v.y - wy * TILE) < TILE * 1.5) {
                tradingVillager = v;
                tradeScroll = 0;
                state = GameState.TRADE;
                return;
            }
        }

        ItemStack held = inventory[selectedSlot];
        if (held != null && isBgBlock(held.id) && world.getBackground(wx, wy) == World.AIR) {
            world.setBackground(wx, wy, held.id);
            if (mode != GameMode.CREATIVE) {
                held.count--;
                if (held.count <= 0) {
                    inventory[selectedSlot] = null;
                }
            }
            if (mp != null) {
                mp.sendBgChange(wx, wy, held.id);
            }
            return;
        }

        if (held != null && world.getBlock(wx, wy) == World.AIR && !ToolUtil.isTool(held.id)) {
            int bx = (int) (player.x / TILE);
            int by = (int) (player.y / TILE);
            boolean inside = (wx == bx || wx == bx + (Player.W / TILE))
                    && (wy == by || wy == by + 1);
            if (!inside) {
                if (mode == GameMode.CREATIVE || held.count > 0) {
                    world.setBlock(wx, wy, held.id);
                    if (mp != null) {
                        mp.sendBlockChange(wx, wy, held.id);
                    }
                    if (mode != GameMode.CREATIVE) {
                        held.count--;
                        if (held.count <= 0) {
                            inventory[selectedSlot] = null;
                        }
                    }
                    Sound.play(Sound.CLICK);
                }
            }
        }
    }

    private void handleLeftClick(int wx, int wy) {
        for (RemotePlayer rp : remotePlayers) {
            if (wx * TILE >= rp.x - 4 && wx * TILE <= rp.x + Player.W + 4
                    && wy * TILE >= rp.y - 4 && wy * TILE <= rp.y + Player.H + 4) {
                ItemStack held = inventory[selectedSlot];
                int dmg = ToolUtil.getSwordDamage(held);
                if (mp != null) {
                    mp.sendDamage(rp.id, dmg);
                }
                floaters.add(new FloatingText("-" + dmg, rp.x, rp.y - 10, new Color(255, 100, 100)));
                return;
            }
        }

        Monster targetMonster = null;
        for (Monster m : monsters) {
            if (wx * TILE >= m.x - 4 && wx * TILE <= m.x + Monster.W + 4
                    && wy * TILE >= m.y - 4 && wy * TILE <= m.y + Monster.H + 4) {
                targetMonster = m;
                break;
            }
        }
        if (targetMonster != null) {
            ItemStack held = inventory[selectedSlot];
            int dmg = ToolUtil.getSwordDamage(held);
            targetMonster.hp -= dmg;
            floaters.add(new FloatingText("-" + dmg, targetMonster.x, targetMonster.y - 10, new Color(255, 100, 100)));
            Sound.play(Sound.HIT);

            if (Modules.TOOLS_WEAR && held != null && ToolUtil.isSword(held.id)) {
                held.damage(1);
                if (held.durability <= 0) {
                    inventory[selectedSlot] = null;
                }
            }

            if (targetMonster.hp <= 0) {
                targetMonster.dead = true;
                Random rnd = new Random();
                addToInventory(ItemStack.of(World.COIN_GOLD, 1 + rnd.nextInt(3)));
                ItemStack loot = targetMonster.getLoot(rnd);
                if (loot != null) {
                    addToInventory(loot);
                }
                addXp(3 + rnd.nextInt(3));
                unlock("first_monster");
            }
            return;
        }

        Animal targetAnimal = null;
        for (Animal a : animals) {
            if (wx * TILE >= a.x - 4 && wx * TILE <= a.x + Animal.W + 4
                    && wy * TILE >= a.y - 4 && wy * TILE <= a.y + Animal.H + 4) {
                targetAnimal = a;
                break;
            }
        }
        if (targetAnimal != null) {
            ItemStack held = inventory[selectedSlot];
            int dmg = ToolUtil.getSwordDamage(held);
            targetAnimal.hp -= dmg;
            targetAnimal.hurtTimer = 20;
            floaters.add(new FloatingText("-" + dmg, targetAnimal.x, targetAnimal.y - 10, new Color(255, 100, 100)));
            Sound.play(Sound.HIT);
            if (targetAnimal.hp <= 0) {
                targetAnimal.dead = true;
                Random rnd = new Random();
                ItemStack drop = targetAnimal.getDrop(rnd);
                if (drop != null) {
                    addToInventory(drop);
                }
                addXp(2);
                unlock("animal");
            }
            return;
        }

        startDigging(wx, wy);
    }

    // ==================== ИНВЕНТАРЬ ====================
    private boolean handleInventoryClick(int mx, int my, boolean isRight) {
        int totalW = INV_COLS * SLOT;
        int totalH = INV_ROWS * SLOT;
        int startX = (SCREEN_W - totalW) / 2 - 100;
        int startY = (SCREEN_H - totalH) / 2;

        int armorPanelW = 3 * SLOT + 30;
        int armorX = startX - armorPanelW - 20;
        int armorY = startY;
        for (int i = 0; i < ARMOR_SLOTS; i++) {
            int sx = armorX;
            int sy = armorY + i * SLOT;
            if (mx >= sx && mx < sx + SLOT && my >= sy && my < sy + SLOT) {
                handleArmorSlotClick(i, isRight);
                return true;
            }
        }

        int craftX = startX + totalW + 40;
        int craftY = startY;
        for (int r = 0; r < 3; r++) {
            for (int c = 0; c < 3; c++) {
                int i = r * 3 + c;
                int sx = craftX + c * SLOT;
                int sy = craftY + r * SLOT;
                if (mx >= sx && mx < sx + SLOT && my >= sy && my < sy + SLOT) {
                    handleSlotClick(craftGrid, i, isRight);
                    return true;
                }
            }
        }

        int arrowX = craftX + 3 * SLOT + 15;
        int resX = arrowX + 50;
        int resY = craftY + SLOT;
        if (mx >= resX && mx < resX + SLOT && my >= resY && my < resY + SLOT) {
            if (craftResult != null && currentRecipe != null) {
                addToInventory(craftResult.copy());
                Crafting.consumeRecipe(currentRecipe, craftGrid);
                Sound.play(Sound.CRAFT);
                unlock("craft");
                return true;
            }
        }

        for (int r = 0; r < INV_ROWS; r++) {
            for (int c = 0; c < INV_COLS; c++) {
                int i = r * INV_COLS + c;
                int sx = startX + c * SLOT;
                int sy = startY + r * SLOT;
                if (mx >= sx && mx < sx + SLOT && my >= sy && my < sy + SLOT) {
                    if (isShiftDown()) {
                        if (activeContainer != null && containerSlots != null) {
                            quickMove(inventory, i, containerSlots);
                        } else if (activeContainer == null && inventory[i] != null
                                && isArmor(inventory[i].id)) {
                            int armorSlot = getArmorSlotFor(inventory[i].id);
                            if (armorSlot >= 0 && armorSlots[armorSlot] == null) {
                                armorSlots[armorSlot] = inventory[i];
                                inventory[i] = null;
                                return true;
                            }
                        }
                        return true;
                    }
                    handleSlotClick(inventory, i, isRight);
                    return true;
                }
            }
        }
        return false;
    }

    private void handleArmorSlotClick(int slot, boolean isRight) {
        if (armorSlots[slot] == null) {
            ItemStack held = inventory[selectedSlot];
            if (held != null && isArmor(held.id) && getArmorSlotFor(held.id) == slot) {
                armorSlots[slot] = held;
                inventory[selectedSlot] = null;
            }
        } else {
            if (inventory[selectedSlot] == null) {
                inventory[selectedSlot] = armorSlots[slot];
                armorSlots[slot] = null;
            } else {
                ItemStack tmp = armorSlots[slot];
                armorSlots[slot] = inventory[selectedSlot];
                inventory[selectedSlot] = tmp;
            }
        }
    }

    private boolean isShiftDown() {
        return keys[KeyEvent.VK_SHIFT];
    }

    private void quickMove(ItemStack[] from, int fromIdx, ItemStack[] to) {
        if (from[fromIdx] == null) {
            return;
        }
        ItemStack stack = from[fromIdx];
        for (int i = 0; i < to.length; i++) {
            if (to[i] != null && to[i].id == stack.id && to[i].count < 999) {
                int space = 999 - to[i].count;
                int move = Math.min(space, stack.count);
                to[i].count += move;
                stack.count -= move;
                if (stack.count <= 0) {
                    from[fromIdx] = null;
                    return;
                }
            }
        }
        for (int i = 0; i < to.length; i++) {
            if (to[i] == null) {
                to[i] = stack;
                from[fromIdx] = null;
                return;
            }
        }
    }

    private void handleSlotClick(ItemStack[] container, int i, boolean isRight) {
        if (container[i] == null) {
            if (draggedStack != null) {
                if (isRight) {
                    container[i] = ItemStack.of(draggedStack.id, 1);
                    draggedStack.count--;
                    if (draggedStack.count <= 0) {
                        draggedStack = null;
                        draggedFromSlot = -1;
                    }
                } else {
                    container[i] = draggedStack;
                    draggedStack = null;
                    draggedFromSlot = -1;
                }
            }
            return;
        }

        if (draggedStack == null) {
            if (isRight) {
                int half = (container[i].count + 1) / 2;
                draggedStack = container[i].copy();
                draggedStack.count = half;
                container[i].count -= half;
                draggedFromSlot = i;
                if (container[i].count <= 0) {
                    container[i] = null;
                }
            } else {
                draggedStack = container[i];
                draggedFromSlot = i;
                container[i] = null;
            }
            return;
        }

        if (container[i].id == draggedStack.id) {
            int space = 999 - container[i].count;
            if (space > 0) {
                int move = Math.min(space, draggedStack.count);
                container[i].count += move;
                draggedStack.count -= move;
                if (draggedStack.count <= 0) {
                    draggedStack = null;
                    draggedFromSlot = -1;
                }
            }
            return;
        }

        ItemStack tmp = container[i];
        container[i] = draggedStack;
        draggedStack = tmp;
        draggedFromSlot = i;
    }

    private boolean handleContainerClick(int mx, int my, boolean isRight) {
        if (containerSlots == null) {
            return false;
        }
        int cols = activeContainer.type == World.CHEST ? 9 : 3;
        int rows = 3;
        int totalW = cols * SLOT;
        int totalH = rows * SLOT;
        int startX = (SCREEN_W - totalW) / 2;
        int startY = (SCREEN_H - totalH) / 2 - 200;
        if (mx < startX || my < startY || mx >= startX + totalW || my >= startY + totalH) {
            return false;
        }

        int c = (mx - startX) / SLOT;
        int r = (my - startY) / SLOT;
        int i = r * cols + c;
        if (i < 0 || i >= containerSlots.length) {
            return false;
        }

        if (activeContainer.type == World.FURNACE && i == 8) {
            ItemStack res = containerSlots[8];
            if (res != null) {
                if (draggedStack == null) {
                    draggedStack = res;
                    containerSlots[8] = null;
                } else if (draggedStack.id == res.id) {
                    draggedStack.count += res.count;
                    containerSlots[8] = null;
                }
            }
            return true;
        }

        if (isShiftDown()) {
            quickMove(containerSlots, i, inventory);
            return true;
        }

        handleSlotClick(containerSlots, i, isRight);
        return true;
    }

    private void returnDragged() {
        if (draggedStack != null) {
            addToInventory(draggedStack);
            draggedStack = null;
        }
        draggedFromSlot = -1;
    }

    private void returnCraftGrid() {
        for (int i = 0; i < craftGrid.length; i++) {
            if (craftGrid[i] != null) {
                addToInventory(craftGrid[i]);
                craftGrid[i] = null;
            }
        }
    }

    private void openContainer(int wx, int wy, int type) {
        for (WorkBlock wb : world.workBlocks) {
            if (wb.x == wx && wb.y == wy) {
                activeContainer = wb;
                containerSlots = wb.slots;
                return;
            }
        }
        int size = type == World.CHEST ? 27 : 9;
        WorkBlock wb = new WorkBlock(wx, wy, type, size);
        world.workBlocks.add(wb);
        activeContainer = wb;
        containerSlots = wb.slots;
    }

    private void doTrade(TradeRecipe r) {
        int gold = countItem(World.COIN_GOLD);
        if (gold < r.priceGold) {
            notify("Недостаточно золота", new Color(255, 100, 100));
            return;
        }
        removeItem(World.COIN_GOLD, r.priceGold);
        addToInventory(ItemStack.of(r.itemId, r.count));

        tradingVillager.xp++;
        if (tradingVillager.xp >= tradingVillager.level * 5) {
            tradingVillager.xp = 0;
            tradingVillager.level++;
            notify("Житель повысил уровень!", new Color(120, 255, 120));
        }
        Sound.play(Sound.TRADE);
        unlock("trade");
    }

    private void deleteDir(File dir) {
        File[] files = dir.listFiles();
        if (files != null) {
            for (File f : files) {
                if (f.isDirectory()) {
                    deleteDir(f);
                } else {
                    f.delete();
                }
            }
        }
        dir.delete();
    }

    // ==================== F11 ====================
    private void toggleFullscreen() {
        try {
            if (!fullscreen) {
                // СОХРАНЯЕМ оконные размеры
                windowedBounds = frame.getBounds();

                // СНАЧАЛА скрываем окно
                frame.setVisible(false);
                frame.dispose();

                // Теперь можно менять undecorated
                frame.setUndecorated(true);

                GraphicsEnvironment ge = GraphicsEnvironment.getLocalGraphicsEnvironment();
                GraphicsDevice gd = ge.getDefaultScreenDevice();

                if (gd.isFullScreenSupported()) {
                    gd.setFullScreenWindow(frame);
                } else {
                    // Резервный вариант — максимальное окно без рамки
                    frame.setBounds(0, 0,
                            Toolkit.getDefaultToolkit().getScreenSize().width,
                            Toolkit.getDefaultToolkit().getScreenSize().height);
                }

                frame.setVisible(true);
                fullscreen = true;
            } else {
                // ВЫХОД из fullscreen
                GraphicsEnvironment ge = GraphicsEnvironment.getLocalGraphicsEnvironment();
                GraphicsDevice gd = ge.getDefaultScreenDevice();
                if (gd.getFullScreenWindow() == frame) {
                    gd.setFullScreenWindow(null);
                }

                frame.setVisible(false);
                frame.dispose();
                frame.setUndecorated(false);

                if (windowedBounds != null) {
                    frame.setBounds(windowedBounds);
                } else {
                    frame.setSize(SCREEN_W, SCREEN_H);
                    frame.setLocationRelativeTo(null);
                }
                frame.setVisible(true);
                fullscreen = false;
            }

            // Пересоздаём буфер и возвращаем фокус
            revalidate();
            repaint();

            SwingUtilities.invokeLater(() -> {
                frame.toFront();
                frame.requestFocus();
                requestFocusInWindow();
            });
        } catch (Exception ex) {
            System.out.println("F11 ошибка: " + ex.getMessage());
            try {
                frame.setVisible(true);
            } catch (Exception ignored) {
            }
            fullscreen = false;
        }
    }

    // ==================== МИРЫ ====================
    private void createWorldWithSettings() {
        long seed = inputSeed.isEmpty() ? new Random().nextLong() : inputSeed.hashCode();
        String worldName = inputSeed.isEmpty() ? "world_" + System.currentTimeMillis() : "world_" + inputSeed;
        currentWorldName = worldName;

        mode = newWorldMode;
        difficulty = newWorldDifficulty;
        currentWorldType = newWorldType;

        world = new World(newWorldWidth, newWorldHeight, seed,
                newWorldType, newWorldOreDensity, newWorldTreeDensity,
                newWorldStructures, difficulty);

        world.name = worldName;
        world.seed = seed;
        world.worldType = newWorldType;
        world.mode = newWorldMode;

        startPlaying();
    }

    private void deleteWorld() {
        if (worldSaves.isEmpty()) {
            return;
        }
        WorldSave ws = worldSaves.get(selectedWorldIndex);
        ws.file.delete();
        refreshWorldSaves();
        if (selectedWorldIndex >= worldSaves.size()) {
            selectedWorldIndex = Math.max(0, worldSaves.size() - 1);
        }
    }

    private void loadSelectedWorld() {
        if (worldSaves.isEmpty()) {
            return;
        }
        WorldSave ws = worldSaves.get(selectedWorldIndex);
        currentWorldName = ws.name;
        try (ObjectInputStream in = new ObjectInputStream(new FileInputStream(ws.file))) {
            this.world = (World) in.readObject();
            if (world.worldType != null) {
                currentWorldType = world.worldType;
            }
            if (world.mode != null) {
                mode = world.mode;
            }
            startPlaying();
        } catch (Exception ex) {
            ex.printStackTrace();
            notify("Ошибка загрузки", new Color(255, 100, 100));
        }
    }

    private void startPlaying() {
        int spawnX = world.getWidth() / 2;
        int spawnY = findSafeSpawnY(spawnX);
        if (spawnY < 5) {
            spawnY = world.getHeight() / 3;
        }
        player = new Player(spawnX * TILE, (spawnY - 3) * TILE);
        player.armorSlots = armorSlots;

        monsters.clear();
        animals.clear();
        villagers.clear();
        floaters.clear();
        chatLog.clear();
        remotePlayers.clear();
        arrows.clear();
        dungeons.clear();
        Arrays.fill(inventory, null);
        Arrays.fill(craftGrid, null);
        Arrays.fill(armorSlots, null);

        if (mode == GameMode.CREATIVE) {
            addToInventory(ItemStack.of(World.WORKBENCH, 1));
            addToInventory(ItemStack.of(World.FURNACE, 1));
            addToInventory(ItemStack.of(World.CHEST, 1));
            addToInventory(ItemStack.of(World.COIN_GOLD, 999));
            addToInventory(ItemStack.of(World.DIRT, 999));
            addToInventory(ItemStack.of(World.STONE, 999));
            addToInventory(ItemStack.of(World.BG_STONE, 999));
        }

        Random rnd = new Random();
        for (int i = 0; i < world.villageX.size(); i++) {
            villagers.add(new Villager(world.villageX.get(i) * TILE,
                    world.villageY.get(i) * TILE, rnd.nextInt(3)));
        }
        if (!villagers.isEmpty()) {
            unlock("village");
        }

        spawnDungeons();

        selectedSlot = 0;
        inventoryOpen = false;
        activeContainer = null;
        containerSlots = null;
        draggedStack = null;
        gameTime = 0;
        state = GameState.PLAYING;
        xp = 0;
        xpLevel = 0;
        xpToNext = 20;
        weatherTimer = 0;
        weather = Weather.CLEAR;

        addChatMessage("Добро пожаловать в TerraPixel " + VERSION + "!", new Color(255, 220, 100));
        addChatMessage("T — чат, E — инвентарь, F11 — fullscreen", new Color(100, 240, 255));
        requestFocusInWindow();
    }

    private void spawnDungeons() {
        if (!newWorldStructures) {
            return;
        }
        try {
            Random rnd = new Random(world.seed + 12345);
            int numDungeons = 2 + rnd.nextInt(2);
            for (int i = 0; i < numDungeons; i++) {
                int dx = 60 + rnd.nextInt(Math.max(1, world.getWidth() - 120));
                int dy = world.getHeight() * 2 / 3 + rnd.nextInt(Math.max(1, world.getHeight() / 5));
                if (dy > world.getHeight() - 15) {
                    dy = world.getHeight() - 15;
                }
                if (dy < 15) {
                    dy = 15;
                }
                if (dx < 15 || dx > world.getWidth() - 15) {
                    continue;
                }
                Dungeon d = new Dungeon(dx, dy, rnd);
                dungeons.add(d);
                d.buildIn(world);
            }
        } catch (Exception ex) {
            System.out.println(">>> Ошибка в spawnDungeons: " + ex.getMessage());
        }
    }

    private int findSafeSpawnY(int x) {
        if (x < 0 || x >= world.getWidth()) {
            return world.getHeight() / 3;
        }
        for (int y = 5; y < world.getHeight() - 3; y++) {
            int b = world.getBlock(x, y);
            if (isSolidBlock(b)) {
                if (!isSolidBlock(world.getBlock(x, y - 1))
                        && !isSolidBlock(world.getBlock(x, y - 2))
                        && !isSolidBlock(world.getBlock(x, y - 3))) {
                    return y;
                }
            }
        }
        return world.getHeight() / 3;
    }

    private boolean isSolidBlock(int b) {
        if (b == World.AIR) {
            return false;
        }
        if (b == World.TORCH) {
            return false;
        }
        if (b == World.DOOR_OPEN) {
            return false;
        }
        if (b >= World.BG_STONE && b <= World.BG_PLANK) {
            return false;
        }
        return true;
    }

    private void respawn() {
        int sx = world.getWidth() / 2;
        int sy = world.findSurface(sx);
        player.x = sx * TILE;
        player.y = (sy - 3) * TILE;
        player.vx = 0;
        player.vy = 0;
        player.hp = player.maxHp;
        player.hunger = player.maxHunger;
        state = GameState.PLAYING;
    }

    private void backToMenu() {
        if (world != null && world.getWidth() > 10 && autoSave) {
            saveCurrentWorld();
        }
        if (mp != null) {
            mp.close();
            mp = null;
        }
        state = GameState.MENU;
        refreshWorldSaves();
    }

    private void saveCurrentWorld() {
        if (world == null || world.getWidth() <= 10) {
            return;
        }
        try (ObjectOutputStream out = new ObjectOutputStream(
                new FileOutputStream("saves/" + currentWorldName + ".world"))) {
            out.writeObject(world);
            notify("Мир сохранён", new Color(120, 255, 120));
        } catch (Exception ex) {
            notify("Ошибка сохранения", new Color(255, 100, 100));
        }
    }

    private boolean isBgBlock(int id) {
        return id == World.BG_STONE || id == World.BG_DIRT
                || id == World.BG_WOOD || id == World.BG_PLANK;
    }

    private boolean isArmor(int id) {
        return Armor.isArmor(id);
    }

    private int getArmorSlotFor(int id) {
        return Armor.getSlot(id);
    }

    private void startMultiplayerHost() {
        try {
            mpStatus = "Запуск сервера...";
            if (world == null || world.getWidth() <= 10) {
                long seed = new Random().nextLong();
                currentWorldName = "mp_host_" + System.currentTimeMillis();
                world = new World(DEFAULT_WORLD_W, DEFAULT_WORLD_H, seed,
                        newWorldType, 1.0, 1.0, true, newWorldDifficulty);
                world.name = currentWorldName;
                world.seed = seed;
                world.worldType = newWorldType;
                world.mode = newWorldMode;
                mode = newWorldMode;
                difficulty = newWorldDifficulty;
                currentWorldType = newWorldType;
            }
            mp = new MultiplayerManager(this);
            mp.startHost(MP_PORT);
            mpHost = true;
            mpStatus = "Сервер запущен на порту " + MP_PORT;
            state = GameState.MP_HOST_WAITING;
            unlock("multiplayer");
        } catch (Exception ex) {
            mpStatus = "Ошибка: " + ex.getMessage();
            notify("Ошибка запуска: " + ex.getMessage(), new Color(255, 100, 100));
        }
    }

    private void startMultiplayerClient() {
        try {
            mp = new MultiplayerManager(this);
            mpHost = false;
            mpStatus = "Подключение к " + mpAddress + "...";
            mp.startClient(mpAddress, MP_PORT);
            unlock("multiplayer");
            world = null;
            player = null;
            state = GameState.LOADING;
        } catch (Exception ex) {
            mpStatus = "Ошибка: " + ex.getMessage();
            state = GameState.MULTIPLAYER;
        }
    }

    // ==================== ПУБЛИЧНЫЕ МЕТОДЫ ДЛЯ MP ====================
    public World getWorld() {
        return world;
    }

    public Player getPlayer() {
        return player;
    }

    public List<RemotePlayer> getRemotePlayers() {
        return remotePlayers;
    }

    public GameMode getMode() {
        return mode;
    }

    public void onRemoteChat(String text) {
        addChatMessage(text, new Color(100, 240, 255));
    }

    public void onRemoteBlockChange(int x, int y, int block) {
        if (world != null && world.getWidth() > 10) {
            world.setBlock(x, y, block);
        }
    }

    public void onRemoteBgChange(int x, int y, int block) {
        if (world != null && world.getWidth() > 10) {
            world.setBackground(x, y, block);
        }
    }

    public void onRemoteDamage(int dmg) {
        if (player != null && !player.godMode) {
            player.hp -= dmg;
            player.hurtCooldown = 30;
            Sound.play(Sound.HURT);
        }
    }

    public void onWorldReceived(World receivedWorld, double spawnX, double spawnY) {
        this.world = receivedWorld;
        if (world.worldType != null) {
            currentWorldType = world.worldType;
        }

        int sx = (int) (spawnX / TILE) + 2;
        if (sx >= world.getWidth() - 2) {
            sx = world.getWidth() / 2;
        }
        int sy = world.findSurface(sx);
        if (sy <= 0 || sy >= world.getHeight() - 3) {
            sy = world.getHeight() / 3;
        }

        player = new Player(sx * TILE, (sy - 3) * TILE);
        player.armorSlots = armorSlots;

        monsters.clear();
        animals.clear();
        villagers.clear();
        floaters.clear();
        remotePlayers.clear();
        arrows.clear();
        dungeons.clear();
        Arrays.fill(inventory, null);
        Arrays.fill(craftGrid, null);
        Arrays.fill(armorSlots, null);

        Random rnd = new Random();
        for (int i = 0; i < world.villageX.size(); i++) {
            villagers.add(new Villager(world.villageX.get(i) * TILE,
                    world.villageY.get(i) * TILE, rnd.nextInt(3)));
        }

        selectedSlot = 0;
        inventoryOpen = false;
        activeContainer = null;
        containerSlots = null;
        draggedStack = null;
        gameTime = 0;
        state = GameState.PLAYING;
        xp = 0;
        xpLevel = 0;
        xpToNext = 20;

        addChatMessage("Мир получен от хоста!", new Color(120, 255, 120));
        mpStatus = "";
        requestFocusInWindow();
    }

    public void onConnectionFailed(String reason) {
        addChatMessage("Не удалось подключиться: " + reason, new Color(255, 100, 100));
        notify("Ошибка подключения", new Color(255, 100, 100));
        if (mp != null) {
            mp.close();
            mp = null;
        }
        world = null;
        player = null;
        mpStatus = "Ошибка: " + reason;
        state = GameState.MULTIPLAYER;
    }

    public void onHostPlayerJoined(String name) {
        mpPlayerList.add(name);
        notify("Игрок подключился: " + name, new Color(120, 255, 120));
        addChatMessage("[СИС] Игрок подключился: " + name, new Color(200, 240, 200));
    }

    public void onHostPlayerLeft(String name) {
        mpPlayerList.remove(name);
        notify("Игрок вышел: " + name, new Color(255, 200, 100));
    }

    public void startPlayingInternal() {
        if (world == null || player == null) {
            state = GameState.MENU;
            return;
        }
        monsters.clear();
        animals.clear();
        floaters.clear();
        chatLog.clear();
        remotePlayers.clear();
        arrows.clear();

        Random rnd = new Random();
        for (int i = 0; i < world.villageX.size(); i++) {
            villagers.add(new Villager(world.villageX.get(i) * TILE,
                    world.villageY.get(i) * TILE, rnd.nextInt(3)));
        }
        if (!villagers.isEmpty()) {
            unlock("village");
        }

        spawnDungeons();

        selectedSlot = 0;
        inventoryOpen = false;
        activeContainer = null;
        containerSlots = null;
        draggedStack = null;
        gameTime = 0;
        state = GameState.PLAYING;
        xp = 0;
        xpLevel = 0;
        xpToNext = 20;

        addChatMessage("Сервер запущен. Игра началась!", new Color(120, 255, 120));
        requestFocusInWindow();
    }
    // ==================== ВВОД: КЛАВИАТУРА ====================

    @Override
    public void keyPressed(KeyEvent e) {
        int code = e.getKeyCode();
        if (code < 256) {
            keys[code] = true;
        }

        if (chatOpen) {
            if (code == KeyEvent.VK_ENTER) {
                if (!chatInput.trim().isEmpty()) {
                    executeChatCommand(chatInput);
                }
                chatInput = "";
                chatOpen = false;
                return;
            }
            if (code == KeyEvent.VK_ESCAPE) {
                chatOpen = false;
                chatInput = "";
                return;
            }
            if (code == KeyEvent.VK_BACK_SPACE) {
                if (!chatInput.isEmpty()) {
                    chatInput = chatInput.substring(0, chatInput.length() - 1);
                }
                return;
            }
            if (code == KeyEvent.VK_TAB) {
                chatChannel = (chatChannel + 1) % 3;
                return;
            }
            char ch = e.getKeyChar();
            if (ch >= 32 && ch < 127 && chatInput.length() < 100) {
                chatInput += ch;
            }
            return;
        }

        if (state == GameState.WORLD_CREATE && typingSeed) {
            if (code == KeyEvent.VK_ENTER) {
                createWorldWithSettings();
                typingSeed = false;
                return;
            }
            if (code == KeyEvent.VK_ESCAPE) {
                typingSeed = false;
                return;
            }
            if (code == KeyEvent.VK_BACK_SPACE) {
                if (!inputSeed.isEmpty()) {
                    inputSeed = inputSeed.substring(0, inputSeed.length() - 1);
                }
                return;
            }
            char ch = e.getKeyChar();
            if (Character.isLetterOrDigit(ch) || ch == '_' || ch == '-') {
                if (inputSeed.length() < 40) {
                    inputSeed += ch;
                }
            }
            return;
        }

        if (state == GameState.MULTIPLAYER && typingMpAddress) {
            if (code == KeyEvent.VK_ENTER) {
                typingMpAddress = false;
                return;
            }
            if (code == KeyEvent.VK_ESCAPE) {
                typingMpAddress = false;
                return;
            }
            if (code == KeyEvent.VK_BACK_SPACE) {
                if (!mpAddress.isEmpty()) {
                    mpAddress = mpAddress.substring(0, mpAddress.length() - 1);
                }
                return;
            }
            char ch = e.getKeyChar();
            if (Character.isLetterOrDigit(ch) || ch == '.' || ch == ':') {
                if (mpAddress.length() < 40) {
                    mpAddress += ch;
                }
            }
            return;
        }

        if (code == KeyEvent.VK_F11) {
            toggleFullscreen();
            return;
        }

        switch (state) {
            case MENU:
                if (code == KeyEvent.VK_ESCAPE) {
                    System.exit(0);
                }
                break;
            case WORLD_SELECT:
                if (code == KeyEvent.VK_ESCAPE) {
                    state = GameState.MENU;
                }
                if (code == KeyEvent.VK_UP) {
                    selectedWorldIndex = Math.max(0, selectedWorldIndex - 1);
                }
                if (code == KeyEvent.VK_DOWN) {
                    selectedWorldIndex = Math.min(Math.max(0, worldSaves.size() - 1), selectedWorldIndex + 1);
                }
                if (code == KeyEvent.VK_N) {
                    state = GameState.WORLD_CREATE;
                    inputSeed = "";
                    typingSeed = true;
                    worldSettingsTab = 0;
                }
                if (code == KeyEvent.VK_DELETE && !worldSaves.isEmpty()) {
                    deleteWorld();
                }
                if (code == KeyEvent.VK_ENTER && !worldSaves.isEmpty()) {
                    loadSelectedWorld();
                }
                break;
            case WORLD_CREATE:
                if (code == KeyEvent.VK_ESCAPE) {
                    state = GameState.WORLD_SELECT;
                }
                if (code == KeyEvent.VK_TAB) {
                    worldSettingsTab = (worldSettingsTab + 1) % 4;
                }
                break;
            case MULTIPLAYER:
                if (code == KeyEvent.VK_ESCAPE) {
                    state = GameState.MENU;
                    typingMpAddress = false;
                }
                break;
            case MP_HOST_WAITING:
                if (code == KeyEvent.VK_ESCAPE) {
                    if (mp != null) {
                        mp.close();
                        mp = null;
                    }
                    state = GameState.MULTIPLAYER;
                }
                if (code == KeyEvent.VK_ENTER) {
                    if (mp != null) {
                        mp.startGameAsHost();

                    }
                }
                break;
            case LOADING:
                if (code == KeyEvent.VK_ESCAPE) {
                    if (mp != null) {
                        mp.close();
                        mp = null;
                    }
                    state = GameState.MULTIPLAYER;
                }
                break;
            case PLAYING:
                handlePlayingKeys(code);
                break;
            case PAUSED:
                if (code == KeyEvent.VK_ESCAPE) {
                    state = GameState.PLAYING;
                }
                if (code == KeyEvent.VK_S) {
                    saveCurrentWorld();
                }
                if (code == KeyEvent.VK_Q) {
                    backToMenu();
                }
                break;
            case DEAD:
                if (code == KeyEvent.VK_R) {
                    respawn();
                }
                if (code == KeyEvent.VK_Q) {
                    backToMenu();
                }
                break;
            case ACHIEVEMENTS:
                if (code == KeyEvent.VK_ESCAPE) {
                    state = GameState.MENU;
                }
                break;
            case SETTINGS:
                if (code == KeyEvent.VK_ESCAPE) {
                    state = GameState.MENU;
                }
                if (code == KeyEvent.VK_S) {
                    saveSettings();
                    notify("Настройки сохранены", new Color(120, 255, 120));
                }
                if (code == KeyEvent.VK_TAB) {
                    settingsTab = (settingsTab + 1) % 3;
                }
                break;
            case RESOURCEPACKS:
                if (code == KeyEvent.VK_ESCAPE) {
                    state = GameState.MENU;
                }
                if (code == KeyEvent.VK_R) {
                    refreshResourcePacks();
                    notify("Ресурспаки обновлены", new Color(120, 255, 120));
                }
                if (code == KeyEvent.VK_DELETE && !resourcePacks.isEmpty()) {
                    if (selectedPackIndex >= 0 && selectedPackIndex < resourcePacks.size()) {
                        ResourcePack rp = resourcePacks.get(selectedPackIndex);
                        if (!rp.isDefault) {
                            rp.close();
                            if (rp.isZip) {
                                rp.folder.delete();
                            } else {
                                deleteDir(rp.folder);
                            }
                            refreshResourcePacks();
                        }
                    }
                }
                if (code == KeyEvent.VK_U) {
                    uploadResourcePack();
                }
                break;
            case TRADE:
                if (code == KeyEvent.VK_ESCAPE) {
                    state = GameState.PLAYING;
                    tradingVillager = null;
                }
                if (code == KeyEvent.VK_UP) {
                    tradeScroll = Math.max(0, tradeScroll - 1);
                }
                if (code == KeyEvent.VK_DOWN && tradingVillager != null) {
                    tradeScroll = Math.min(Math.max(0, tradingVillager.getRecipes().size() - 7), tradeScroll + 1);
                }
                break;
        }
    }

    private void handlePlayingKeys(int code) {
        if (code == KeyEvent.VK_T) {
            chatOpen = true;
            chatInput = "";
            chatChannel = 0;
            return;
        }
        if (code == KeyEvent.VK_SLASH) {
            chatOpen = true;
            chatInput = "/";
            return;
        }

        if (code == KeyEvent.VK_E) {
            inventoryOpen = !inventoryOpen;
            if (!inventoryOpen) {
                returnDragged();
                returnCraftGrid();
            }
            return;
        }

        if (code == KeyEvent.VK_ESCAPE) {
            if (activeContainer != null) {
                activeContainer = null;
                containerSlots = null;
            } else if (inventoryOpen) {
                inventoryOpen = false;
                returnDragged();
                returnCraftGrid();
            } else {
                state = GameState.PAUSED;
            }
            return;
        }

        if (code == KeyEvent.VK_M) {
            if (mode == GameMode.SURVIVAL) {
                mode = GameMode.CREATIVE;
            } else if (mode == GameMode.CREATIVE) {
                mode = GameMode.SURVIVAL;
            }
            notify("Режим: " + mode, new Color(100, 240, 240));
            return;
        }

        if (code >= KeyEvent.VK_1 && code <= KeyEvent.VK_9) {
            selectedSlot = code - KeyEvent.VK_1;
            return;
        }
        if (code == KeyEvent.VK_F5) {
            saveCurrentWorld();
            return;
        }
        if (code == KeyEvent.VK_F3) {
            showCoordinates = !showCoordinates;
            return;
        }

        if (code == KeyEvent.VK_Q) {
            ItemStack held = inventory[selectedSlot];
            if (held != null) {
                held.count--;
                if (held.count <= 0) {
                    inventory[selectedSlot] = null;
                }
                floaters.add(new FloatingText("Выброшено", player.x, player.y - 20, new Color(200, 200, 200)));
            }
            return;
        }
    }

    @Override
    public void keyReleased(KeyEvent e) {
        if (e.getKeyCode() < 256) {
            keys[e.getKeyCode()] = false;
        }
    }

    @Override
    public void keyTyped(KeyEvent e) {
    }

    // ==================== ВВОД: МЫШЬ ====================
    @Override
    public void mousePressed(MouseEvent e) {
        mouseX = e.getX();
        mouseY = e.getY();
        boolean isLeft = SwingUtilities.isLeftMouseButton(e);
        boolean isRight = SwingUtilities.isRightMouseButton(e);
        if (isLeft) {
            mouseDown = true;
        }
        if (isRight) {
            rightMouseDown = true;
        }

        if (state == GameState.PLAYING && inventoryOpen) {
            handleInventoryClick(mouseX, mouseY, isRight);
            return;
        }
        if (state == GameState.PLAYING && activeContainer != null) {
            handleContainerClick(mouseX, mouseY, isRight);
            return;
        }

        handleClick(e);
    }

    @Override
    public void mouseReleased(MouseEvent e) {
        if (SwingUtilities.isLeftMouseButton(e)) {
            mouseDown = false;
        }
        if (SwingUtilities.isRightMouseButton(e)) {
            rightMouseDown = false;
        }
        if (state == GameState.PLAYING) {
            digProgress = 0;
        }
    }

    @Override
    public void mouseMoved(MouseEvent e) {
        mouseX = e.getX();
        mouseY = e.getY();
    }

    @Override
    public void mouseDragged(MouseEvent e) {
        mouseX = e.getX();
        mouseY = e.getY();
    }

    @Override
    public void mouseClicked(MouseEvent e) {
    }

    @Override
    public void mouseEntered(MouseEvent e) {
    }

    @Override
    public void mouseExited(MouseEvent e) {
    }

    @Override
    public void mouseWheelMoved(MouseWheelEvent e) {
        if (state == GameState.TRADE && tradingVillager != null) {
            int notches = e.getWheelRotation();
            tradeScroll = Math.max(0, Math.min(tradingVillager.getRecipes().size() - 7, tradeScroll + notches));
            return;
        }
        if (state == GameState.PLAYING) {
            int notches = e.getWheelRotation();
            selectedSlot = (selectedSlot + notches + INV_COLS) % INV_COLS;
        }
    }

    // ==================== ЧАТ-КОМАНДЫ ====================
    private void executeChatCommand(String text) {
        String chTag = "";
        switch (chatChannel) {
            case 0:
                chTag = "[ВСЕ] ";
                break;
            case 1:
                chTag = "[ЛОК] ";
                break;
            case 2:
                chTag = "[СИС] ";
                break;
        }

        if (!text.startsWith("/")) {
            String msg = chTag + "<Игрок> " + text;
            addChatMessage(msg, Color.WHITE);
            if (mp != null) {
                mp.sendChat(msg);
            }
            return;
        }

        addChatMessage("<Игрок> " + text, new Color(200, 200, 200));
        String[] parts = text.substring(1).split("\\s+");
        String cmd = parts[0].toLowerCase();

        try {
            switch (cmd) {
                case "help":
                    addChatMessage("/give /heal /god /fly /tp /time /weather", Color.YELLOW);
                    addChatMessage("/spawn /animal /killall /clear /save /xp", Color.YELLOW);
                    addChatMessage("/unlock /seed /coords /gamemode /difficulty", Color.YELLOW);
                    break;
                case "give": {
                    if (parts.length < 2) {
                        addChatMessage("Использование: /give <блок> [N]", Color.RED);
                        break;
                    }
                    int id = parseBlockId(parts[1]);
                    int cnt = parts.length >= 3 ? Integer.parseInt(parts[2]) : 1;
                    if (id < 0) {
                        addChatMessage("Неизвестный блок", Color.RED);
                        break;
                    }
                    addToInventory(ItemStack.of(id, cnt));
                    addChatMessage("Выдано: " + cnt + "× " + World.blockName(id), Color.GREEN);
                    break;
                }
                case "heal":
                    player.hp = player.maxHp;
                    player.hunger = player.maxHunger;
                    addChatMessage("Здоровье восстановлено", Color.GREEN);
                    break;
                case "god":
                    player.godMode = !player.godMode;
                    addChatMessage("Бессмертие: " + (player.godMode ? "ВКЛ" : "ВЫКЛ"), Color.GREEN);
                    break;
                case "fly":
                    player.flyMode = !player.flyMode;
                    addChatMessage("Полёт: " + (player.flyMode ? "ВКЛ" : "ВЫКЛ"), Color.GREEN);
                    break;
                case "tp": {
                    if (parts.length < 3) {
                        addChatMessage("/tp <x> <y>", Color.RED);
                        break;
                    }
                    player.x = Double.parseDouble(parts[1]) * TILE;
                    player.y = Double.parseDouble(parts[2]) * TILE;
                    player.vx = 0;
                    player.vy = 0;
                    break;
                }
                case "time": {
                    if (parts.length < 2) {
                        break;
                    }
                    if (parts[1].equals("day")) {
                        gameTime = 0;
                    } else if (parts[1].equals("night")) {
                        gameTime = DAY_LENGTH / 2;
                    }
                    addChatMessage("Время установлено", Color.GREEN);
                    break;
                }
                case "weather": {
                    if (parts.length < 2) {
                        break;
                    }
                    switch (parts[1].toLowerCase()) {
                        case "clear":
                            weather = Weather.CLEAR;
                            break;
                        case "rain":
                            weather = Weather.RAIN;
                            break;
                        case "snow":
                            weather = Weather.SNOW;
                            break;
                        case "storm":
                            weather = Weather.STORM;
                            break;
                        case "sandstorm":
                            weather = Weather.SANDSTORM;
                            break;
                    }
                    break;
                }
                case "spawn": {
                    if (parts.length < 2) {
                        break;
                    }
                    int type = parseMonsterType(parts[1]);
                    int cnt = parts.length >= 3 ? Integer.parseInt(parts[2]) : 1;
                    for (int i = 0; i < cnt; i++) {
                        monsters.add(new Monster(player.x + (Math.random() * 10 - 5) * TILE,
                                player.y - 2 * TILE, type));
                    }
                    addChatMessage("Спавн: " + cnt, Color.GREEN);
                    break;
                }
                case "animal": {
                    if (parts.length < 2) {
                        break;
                    }
                    int type = parseAnimalType(parts[1]);
                    int cnt = parts.length >= 3 ? Integer.parseInt(parts[2]) : 1;
                    for (int i = 0; i < cnt; i++) {
                        animals.add(new Animal(player.x + (Math.random() * 10 - 5) * TILE,
                                player.y - 2 * TILE, type));
                    }
                    addChatMessage("Спавн: " + cnt, Color.GREEN);
                    break;
                }
                case "killall":
                    monsters.clear();
                    addChatMessage("Монстры удалены", Color.GREEN);
                    break;
                case "clear":
                    Arrays.fill(inventory, null);
                    Arrays.fill(armorSlots, null);
                    break;
                case "save":
                    saveCurrentWorld();
                    break;
                case "xp": {
                    int n = parts.length >= 2 ? Integer.parseInt(parts[1]) : 100;
                    addXp(n);
                    break;
                }
                case "unlock":
                    if (parts.length >= 2 && parts[1].equals("all")) {
                        for (Achievement a : achievements) {
                            a.unlocked = true;
                        }
                    }
                    break;
                case "seed":
                    addChatMessage("Сид: " + world.seed, Color.CYAN);
                    break;
                case "coords":
                    addChatMessage("X=" + (int) (player.x / TILE) + " Y=" + (int) (player.y / TILE), Color.CYAN);
                    break;
                case "gamemode": {
                    if (parts.length < 2) {
                        break;
                    }
                    switch (parts[1].toLowerCase()) {
                        case "survival":
                            mode = GameMode.SURVIVAL;
                            break;
                        case "creative":
                            mode = GameMode.CREATIVE;
                            break;
                        case "hardcore":
                            mode = GameMode.HARDCORE;
                            break;
                    }
                    break;
                }
                case "difficulty": {
                    if (parts.length < 2) {
                        break;
                    }
                    switch (parts[1].toLowerCase()) {
                        case "peaceful":
                            difficulty = Difficulty.PEACEFUL;
                            break;
                        case "easy":
                            difficulty = Difficulty.EASY;
                            break;
                        case "normal":
                            difficulty = Difficulty.NORMAL;
                            break;
                        case "hard":
                            difficulty = Difficulty.HARD;
                            break;
                    }
                    break;
                }
                default:
                    addChatMessage("Неизвестная команда: /" + cmd, Color.RED);
            }
        } catch (Exception ex) {
            addChatMessage("Ошибка: " + ex.getMessage(), Color.RED);
        }
    }

    private int parseMonsterType(String name) {
        switch (name.toLowerCase()) {
            case "zombie":
                return 0;
            case "skeleton":
                return 1;
            case "slime":
                return 2;
            case "creeper":
                return 3;
            case "spider":
                return 4;
            default:
                return 0;
        }
    }

    private int parseAnimalType(String name) {
        switch (name.toLowerCase()) {
            case "pig":
                return 0;
            case "cow":
                return 1;
            case "sheep":
                return 2;
            case "chicken":
                return 3;
            default:
                return 0;
        }
    }

    private int parseBlockId(String name) {
        switch (name.toLowerCase()) {
            case "dirt":
                return World.DIRT;
            case "stone":
                return World.STONE;
            case "grass":
                return World.GRASS;
            case "sand":
                return World.SAND;
            case "wood":
                return World.WOOD;
            case "leaves":
                return World.LEAVES;
            case "coal":
                return World.COAL;
            case "iron":
                return World.IRON;
            case "gold":
                return World.GOLD;
            case "diamond":
                return World.DIAMOND;
            case "chest":
                return World.CHEST;
            case "furnace":
                return World.FURNACE;
            case "workbench":
                return World.WORKBENCH;
            case "torch":
                return World.TORCH;
            case "plank":
                return World.PLANK;
            case "stick":
                return World.STICK;
            case "iron_ingot":
                return World.IRON_INGOT;
            case "gold_ingot":
                return World.GOLD_INGOT;
            case "diamond_gem":
                return World.DIAMOND_GEM;
            case "coin":
                return World.COIN_GOLD;
            case "snow":
                return World.SNOW;
            case "ice":
                return World.ICE;
            case "glass":
                return World.GLASS;
            case "bookshelf":
                return World.BOOKSHELF;
            case "lantern":
                return World.LANTERN;
            case "ladder":
                return World.LADDER;
            case "bed":
                return World.BED;
            case "sign":
                return World.SIGN;
            case "sword_wood":
                return World.SWORD_WOOD;
            case "sword_stone":
                return World.SWORD_STONE;
            case "sword_iron":
                return World.SWORD_IRON;
            case "sword_diamond":
                return World.SWORD_DIAMOND;
            case "pick_wood":
                return World.PICK_WOOD;
            case "pick_stone":
                return World.PICK_STONE;
            case "pick_iron":
                return World.PICK_IRON;
            case "pick_diamond":
                return World.PICK_DIAMOND;
            case "axe_wood":
                return World.AXE_WOOD;
            case "axe_stone":
                return World.AXE_STONE;
            case "axe_iron":
                return World.AXE_IRON;
            case "axe_diamond":
                return World.AXE_DIAMOND;
            case "shovel_wood":
                return World.SHOVEL_WOOD;
            case "shovel_stone":
                return World.SHOVEL_STONE;
            case "shovel_iron":
                return World.SHOVEL_IRON;
            case "shovel_diamond":
                return World.SHOVEL_DIAMOND;
            case "bow":
                return World.BOW;
            case "arrow":
                return World.ARROW;
            case "helmet_iron":
                return World.HELMET_IRON;
            case "chest_iron":
                return World.CHESTPLATE_IRON;
            case "legs_iron":
                return World.LEGGINGS_IRON;
            case "boots_iron":
                return World.BOOTS_IRON;
            case "helmet_diamond":
                return World.HELMET_DIAMOND;
            case "apple":
                return World.APPLE;
            case "bread":
                return World.BREAD;
            case "meat":
                return World.MEAT;
            case "slime_ball":
                return World.SLIME_BALL;
            case "command_block":
                return World.COMMAND_BLOCK;
            default:
                return -1;
        }
    }

    // ==================== МУЛЬТИПЛЕЕР ====================
    static class MultiplayerManager {

        private final TerraPixel game;
        private ServerSocket serverSocket;
        private Socket socket;
        private ObjectOutputStream out;
        private ObjectInputStream in;
        private volatile boolean host = false;
        private volatile boolean running = false;
        private volatile boolean gameStarted = false;

        private final Map<Integer, ClientInfo> clients = new ConcurrentHashMap<>();
        private int nextClientId = 1;
        private final Object sendLock = new Object();

        MultiplayerManager(TerraPixel game) {
            this.game = game;
        }

        boolean isHost() {
            return host;
        }

        void startHost(int port) throws IOException {
            host = true;
            running = true;
            serverSocket = new ServerSocket();
            serverSocket.setReuseAddress(true);
            serverSocket.bind(new InetSocketAddress(port));

            Thread acceptThread = new Thread(() -> {
                while (running) {
                    try {
                        Socket s = serverSocket.accept();
                        s.setTcpNoDelay(true);
                        s.setKeepAlive(true);
                        int id = nextClientId++;
                        ClientInfo ci = new ClientInfo(id, s);
                        clients.put(id, ci);
                        new Thread(() -> handleClient(ci), "MP-Client-" + id).start();
                    } catch (Exception e) {
                        if (running) {
                            System.err.println("MP: " + e.getMessage());
                        }
                    }
                }
            }, "MP-Accept");
            acceptThread.setDaemon(true);
            acceptThread.start();
        }

        private void handleClient(ClientInfo ci) {
            try {
                ci.out = new ObjectOutputStream(ci.socket.getOutputStream());
                ci.out.flush();
                ci.in = new ObjectInputStream(ci.socket.getInputStream());

                Object hello = ci.in.readObject();
                if (hello instanceof HelloPacket) {
                    ci.name = ((HelloPacket) hello).playerName;
                    game.onHostPlayerJoined(ci.name);
                }

                WelcomePacket wp = new WelcomePacket();
                wp.clientId = ci.id;
                wp.serverName = "TerraPixel Host";
                synchronized (sendLock) {
                    ci.out.writeObject(wp);
                    ci.out.flush();
                }

                if (gameStarted && game.getWorld() != null && game.getPlayer() != null) {
                    WorldSyncPacket wsp = new WorldSyncPacket();
                    wsp.world = game.getWorld();
                    wsp.spawnX = game.getPlayer().x;
                    wsp.spawnY = game.getPlayer().y;
                    synchronized (sendLock) {
                        ci.out.writeObject(wsp);
                        ci.out.flush();
                    }
                }

                while (running && !ci.socket.isClosed()) {
                    Object obj = ci.in.readObject();
                    processPacket(obj, ci.id);
                }
            } catch (Exception e) {
                if (running) {
                    System.err.println("MP client " + ci.id + ": " + e.getMessage());
                }
            } finally {
                clients.remove(ci.id);
                try {
                    ci.socket.close();
                } catch (Exception ignored) {
                }
                game.onHostPlayerLeft(ci.name);
            }
        }

        void startGameAsHost() {
            gameStarted = true;
            if (game.getWorld() != null && game.getPlayer() != null) {
                WorldSyncPacket wsp = new WorldSyncPacket();
                wsp.world = game.getWorld();
                wsp.spawnX = game.getPlayer().x;
                wsp.spawnY = game.getPlayer().y;
                broadcast(wsp, -1);
            }
            game.startPlayingInternal();
        }

        void startClient(String address, int port) {
            host = false;
            running = true;
            new Thread(() -> {
                int attempts = 0;
                while (attempts < 3 && running) {
                    try {
                        socket = new Socket();
                        socket.connect(new InetSocketAddress(address, port), 5000);
                        socket.setTcpNoDelay(true);
                        socket.setKeepAlive(true);
                        socket.setSoTimeout(20000);

                        out = new ObjectOutputStream(socket.getOutputStream());
                        out.flush();
                        in = new ObjectInputStream(socket.getInputStream());

                        HelloPacket hello = new HelloPacket();
                        hello.playerName = "Клиент" + (System.currentTimeMillis() % 1000);
                        out.writeObject(hello);
                        out.flush();

                        Object welcome = in.readObject();
                        if (welcome instanceof WelcomePacket) {
                            socket.setSoTimeout(0);
                            game.mpStatus = "Подключено к " + ((WelcomePacket) welcome).serverName;
                        }

                        new Thread(this::clientLoop, "MP-Client-Loop").start();
                        return;
                    } catch (Exception e) {
                        attempts++;
                        if (attempts >= 3) {
                            final String msg = e.getMessage() != null ? e.getMessage() : e.getClass().getSimpleName();
                            SwingUtilities.invokeLater(() -> game.onConnectionFailed(msg));
                            close();
                            return;
                        }
                        try {
                            Thread.sleep(1000);
                        } catch (Exception ignored) {
                        }
                    }
                }
            }, "MP-Connect").start();
        }

        private void clientLoop() {
            try {
                while (running && socket != null && !socket.isClosed()) {
                    Object obj = in.readObject();
                    processPacket(obj, -1);
                }
            } catch (Exception e) {
                if (running) {
                    SwingUtilities.invokeLater(() -> game.onRemoteChat("[СИС] Соединение потеряно"));
                }
            }
        }

        private void processPacket(Object obj, int fromClient) {
            if (obj instanceof WorldSyncPacket) {
                WorldSyncPacket wsp = (WorldSyncPacket) obj;
                SwingUtilities.invokeLater(() -> game.onWorldReceived(wsp.world, wsp.spawnX, wsp.spawnY));
                return;
            }
            if (obj instanceof PlayerUpdatePacket) {
                PlayerUpdatePacket p = (PlayerUpdatePacket) obj;
                SwingUtilities.invokeLater(() -> {
                    RemotePlayer rp = null;
                    for (RemotePlayer r : game.getRemotePlayers()) {
                        if (r.id == p.playerId) {
                            rp = r;
                            break;
                        }
                    }
                    if (rp == null) {
                        rp = new RemotePlayer(p.playerId, p.x, p.y);
                        game.getRemotePlayers().add(rp);
                    }
                    rp.updatePosition(p.x, p.y, p.facing);
                    if (host && fromClient != -1) {
                        broadcast(p, fromClient);
                    }
                });
            } else if (obj instanceof ChatPacket) {
                ChatPacket c = (ChatPacket) obj;
                SwingUtilities.invokeLater(() -> game.onRemoteChat(c.text));
                if (host && fromClient != -1) {
                    broadcast(c, fromClient);
                }
            } else if (obj instanceof BlockChangePacket) {
                BlockChangePacket b = (BlockChangePacket) obj;
                SwingUtilities.invokeLater(() -> game.onRemoteBlockChange(b.x, b.y, b.block));
                if (host && fromClient != -1) {
                    broadcast(b, fromClient);
                }
            } else if (obj instanceof BgChangePacket) {
                BgChangePacket b = (BgChangePacket) obj;
                SwingUtilities.invokeLater(() -> game.onRemoteBgChange(b.x, b.y, b.block));
                if (host && fromClient != -1) {
                    broadcast(b, fromClient);
                }
            } else if (obj instanceof DamagePacket) {
                if (host && fromClient != -1) {
                    broadcast(obj, fromClient);
                }
            }
        }

        void tick(Player player) {
            if (!running || player == null) {
                return;
            }
            PlayerUpdatePacket p = new PlayerUpdatePacket();
            p.playerId = host ? 0 : 999;
            p.x = player.x;
            p.y = player.y;
            p.facing = player.facing;
            if (host) {
                broadcast(p, -1);
            } else {
                sendToServer(p);
            }
        }

        void updateRemotePlayers(List<RemotePlayer> rps) {
            for (RemotePlayer rp : rps) {
                rp.tick();
            }
        }

        void sendChat(String text) {
            ChatPacket c = new ChatPacket();
            c.text = text;
            if (host) {
                broadcast(c, -1);
            } else {
                sendToServer(c);
            }
        }

        void sendBlockChange(int x, int y, int block) {
            BlockChangePacket b = new BlockChangePacket();
            b.x = x;
            b.y = y;
            b.block = block;
            if (host) {
                broadcast(b, -1);
            } else {
                sendToServer(b);
            }
        }

        void sendBgChange(int x, int y, int block) {
            BgChangePacket b = new BgChangePacket();
            b.x = x;
            b.y = y;
            b.block = block;
            if (host) {
                broadcast(b, -1);
            } else {
                sendToServer(b);
            }
        }

        void sendDamage(int targetId, int dmg) {
            DamagePacket d = new DamagePacket();
            d.targetId = targetId;
            d.dmg = dmg;
            if (host) {
                broadcast(d, -1);
            } else {
                sendToServer(d);
            }
        }

        private void sendToServer(Object packet) {
            if (out == null) {
                return;
            }
            try {
                synchronized (sendLock) {
                    out.writeObject(packet);
                    out.flush();
                    out.reset();
                }
            } catch (Exception ignored) {
            }
        }

        private void broadcast(Object packet, int exceptClientId) {
            for (ClientInfo ci : clients.values()) {
                if (ci.id == exceptClientId) {
                    continue;
                }
                if (ci.out == null) {
                    continue;
                }
                try {
                    synchronized (sendLock) {
                        ci.out.writeObject(packet);
                        ci.out.flush();
                        ci.out.reset();
                    }
                } catch (Exception ignored) {
                }
            }
        }

        void tickHostWaiting() {
        }

        void close() {
            running = false;
            try {
                if (serverSocket != null) {
                    serverSocket.close();

                }
            } catch (Exception ignored) {
            }
            try {
                if (socket != null) {
                    socket.close();

                }
            } catch (Exception ignored) {
            }
            for (ClientInfo ci : clients.values()) {
                try {
                    ci.socket.close();
                } catch (Exception ignored) {
                }
            }
            clients.clear();
        }

        static class ClientInfo {

            int id;
            String name = "Игрок";
            Socket socket;
            ObjectOutputStream out;
            ObjectInputStream in;

            ClientInfo(int id, Socket s) {
                this.id = id;
                this.socket = s;
            }
        }
    }

    // ==================== ПАКЕТЫ ====================
    static class HelloPacket implements Serializable {

        private static final long serialVersionUID = 1L;
        String playerName;
    }

    static class WelcomePacket implements Serializable {

        private static final long serialVersionUID = 1L;
        int clientId;
        String serverName;
    }

    static class WorldSyncPacket implements Serializable {

        private static final long serialVersionUID = 3L;
        World world;
        double spawnX, spawnY;
    }

    static class PlayerUpdatePacket implements Serializable {

        private static final long serialVersionUID = 3L;
        int playerId;
        double x, y;
        int facing;
    }

    static class ChatPacket implements Serializable {

        private static final long serialVersionUID = 3L;
        String text;
    }

    static class BlockChangePacket implements Serializable {

        private static final long serialVersionUID = 3L;
        int x, y, block;
    }

    static class BgChangePacket implements Serializable {

        private static final long serialVersionUID = 3L;
        int x, y, block;
    }

    static class DamagePacket implements Serializable {

        private static final long serialVersionUID = 3L;
        int targetId, dmg;
    }

    // ==================== MODULES ====================
    static class Modules {

        public static final boolean SHOW_BACKGROUND = true;
        public static final boolean AUTO_GEN_BG = true;
        public static final boolean HUNGER_SYSTEM = true;
        public static final boolean FALL_DAMAGE = true;
        public static final boolean TOOLS_WEAR = true;
        public static final boolean DAY_NIGHT_MOBS = true;
    }
    // ==================== RESOURCE PACK ====================

    static class ResourcePack {

        File folder;
        boolean isZip = false;
        ZipFile zipFile = null;
        String name = "pack";
        String description = "";
        String author = "";
        String version = "1.0";
        boolean active = false;
        boolean isDefault = false;

        InputStream getResource(String relativePath) {
            if (!isZip && folder != null) {
                File f = new File(folder, relativePath);
                if (f.exists() && f.isFile()) {
                    try {
                        return new FileInputStream(f);
                    } catch (Exception e) {
                        return null;
                    }
                }
                return null;
            }
            if (isZip && zipFile != null) {
                ZipEntry entry = zipFile.getEntry(relativePath);
                if (entry != null) {
                    try {
                        return zipFile.getInputStream(entry);
                    } catch (Exception e) {
                        return null;
                    }
                }
            }
            return null;
        }

        boolean hasResource(String relativePath) {
            if (!isZip && folder != null) {
                return new File(folder, relativePath).exists();
            }
            if (isZip && zipFile != null) {
                return zipFile.getEntry(relativePath) != null;
            }
            return false;
        }

        void close() {
            if (zipFile != null) {
                try {
                    zipFile.close();
                } catch (Exception ignored) {
                }
                zipFile = null;
            }
        }
    }

    // ==================== PIXEL FONT ====================
    static class PixelFont {

        private static final Map<String, Font> cache = new HashMap<>();
        private static Font customFont = null;

        static {
            try {
                File f = new File("resources/fonts/pixel_font.ttf");
                if (f.exists()) {
                    customFont = Font.createFont(Font.TRUETYPE_FONT, f);
                } else {
                    InputStream is = PixelFont.class.getResourceAsStream("/resources/fonts/pixel_font.ttf");
                    if (is != null) {
                        customFont = Font.createFont(Font.TRUETYPE_FONT, is);
                        is.close();
                    }
                }
            } catch (Exception ignored) {
            }
        }

        public static Font font(int size, int style) {
            String key = size + "_" + style;
            Font f = cache.get(key);
            if (f != null) {
                return f;
            }

            if (customFont != null) {
                f = customFont.deriveFont(style, (float) size);
            } else {
                String[] preferred = {"Press Start 2P", "Pixel", "Minecraft",
                    "Fixedsys", "Terminal", "Courier New", "Monospaced"};
                String[] avail = GraphicsEnvironment.getLocalGraphicsEnvironment()
                        .getAvailableFontFamilyNames();
                Set<String> availSet = new HashSet<>(Arrays.asList(avail));
                String chosen = "Monospaced";
                for (String p : preferred) {
                    if (availSet.contains(p)) {
                        chosen = p;
                        break;
                    }
                }
                f = new Font(chosen, style, size);
            }
            cache.put(key, f);
            return f;
        }

        public static void reload() {
            cache.clear();
            customFont = null;
            try {
                File f = new File("resources/fonts/pixel_font.ttf");
                if (f.exists()) {
                    customFont = Font.createFont(Font.TRUETYPE_FONT, f);
                } else {
                    InputStream is = PixelFont.class.getResourceAsStream("/resources/fonts/pixel_font.ttf");
                    if (is != null) {
                        customFont = Font.createFont(Font.TRUETYPE_FONT, is);
                        is.close();
                    }
                }
            } catch (Exception ignored) {
            }
        }
    }

    // ==================== ITEMSTACK ====================
    static class ItemStack implements Serializable {

        private static final long serialVersionUID = 3L;
        int id;
        int count;
        int durability = -1;
        int maxDurability = -1;

        ItemStack(int id, int count) {
            this.id = id;
            this.count = count;
            int dur = ToolUtil.getDurability(id);
            if (dur > 0) {
                this.durability = dur;
                this.maxDurability = dur;
            }
        }

        static ItemStack of(int id, int count) {
            return new ItemStack(id, count);
        }

        ItemStack copy() {
            ItemStack s = new ItemStack(id, count);
            s.durability = this.durability;
            s.maxDurability = this.maxDurability;
            return s;
        }

        void damage(int amount) {
            if (durability > 0) {
                durability -= amount;
                if (durability < 0) {
                    durability = 0;
                }
            }
        }

        boolean isBroken() {
            return maxDurability > 0 && durability <= 0;
        }
    }

    // ==================== ARMOR ====================
    static class Armor {

        static boolean isArmor(int id) {
            return getSlot(id) >= 0;
        }

        static int getSlot(int id) {
            if (id == World.HELMET_IRON || id == World.HELMET_DIAMOND
                    || id == World.HELMET_GOLD || id == World.HELMET_LEATHER) {
                return 0;
            }
            if (id == World.CHESTPLATE_IRON || id == World.CHESTPLATE_DIAMOND
                    || id == World.CHESTPLATE_GOLD || id == World.CHESTPLATE_LEATHER) {
                return 1;
            }
            if (id == World.LEGGINGS_IRON || id == World.LEGGINGS_DIAMOND
                    || id == World.LEGGINGS_GOLD || id == World.LEGGINGS_LEATHER) {
                return 2;
            }
            if (id == World.BOOTS_IRON || id == World.BOOTS_DIAMOND
                    || id == World.BOOTS_GOLD || id == World.BOOTS_LEATHER) {
                return 3;
            }
            return -1;
        }

        static int getArmorPoints(int id) {
            switch (id) {
                case World.HELMET_LEATHER:
                    return 1;
                case World.CHESTPLATE_LEATHER:
                    return 2;
                case World.LEGGINGS_LEATHER:
                    return 1;
                case World.BOOTS_LEATHER:
                    return 1;
                case World.HELMET_GOLD:
                    return 2;
                case World.CHESTPLATE_GOLD:
                    return 3;
                case World.LEGGINGS_GOLD:
                    return 2;
                case World.BOOTS_GOLD:
                    return 1;
                case World.HELMET_IRON:
                    return 3;
                case World.CHESTPLATE_IRON:
                    return 4;
                case World.LEGGINGS_IRON:
                    return 3;
                case World.BOOTS_IRON:
                    return 2;
                case World.HELMET_DIAMOND:
                    return 4;
                case World.CHESTPLATE_DIAMOND:
                    return 5;
                case World.LEGGINGS_DIAMOND:
                    return 4;
                case World.BOOTS_DIAMOND:
                    return 3;
                default:
                    return 0;
            }
        }
    }

    // ==================== TOOL UTIL ====================
    static class ToolUtil {

        static boolean isPickaxe(int id) {
            return id == World.PICK_WOOD || id == World.PICK_STONE
                    || id == World.PICK_IRON || id == World.PICK_DIAMOND;
        }

        static boolean isAxe(int id) {
            return id == World.AXE_WOOD || id == World.AXE_STONE
                    || id == World.AXE_IRON || id == World.AXE_DIAMOND;
        }

        static boolean isShovel(int id) {
            return id == World.SHOVEL_WOOD || id == World.SHOVEL_STONE
                    || id == World.SHOVEL_IRON || id == World.SHOVEL_DIAMOND;
        }

        static boolean isSword(int id) {
            return id == World.SWORD_WOOD || id == World.SWORD_STONE
                    || id == World.SWORD_IRON || id == World.SWORD_DIAMOND;
        }

        static boolean isTool(int id) {
            return isPickaxe(id) || isAxe(id) || isShovel(id) || isSword(id);
        }

        static boolean isBow(int id) {
            return id == World.BOW;
        }

        static int getDurability(int id) {
            switch (id) {
                case World.PICK_WOOD:
                case World.AXE_WOOD:
                case World.SHOVEL_WOOD:
                case World.SWORD_WOOD:
                    return 60;
                case World.PICK_STONE:
                case World.AXE_STONE:
                case World.SHOVEL_STONE:
                case World.SWORD_STONE:
                    return 130;
                case World.PICK_IRON:
                case World.AXE_IRON:
                case World.SHOVEL_IRON:
                case World.SWORD_IRON:
                    return 250;
                case World.PICK_DIAMOND:
                case World.AXE_DIAMOND:
                case World.SHOVEL_DIAMOND:
                case World.SWORD_DIAMOND:
                    return 1500;
                case World.BOW:
                    return 380;
                default:
                    return 0;
            }
        }

        static int getToolPower(ItemStack s) {
            if (s == null) {
                return 1;
            }
            switch (s.id) {
                case World.PICK_WOOD:
                case World.AXE_WOOD:
                case World.SHOVEL_WOOD:
                    return 2;
                case World.PICK_STONE:
                case World.AXE_STONE:
                case World.SHOVEL_STONE:
                    return 3;
                case World.PICK_IRON:
                case World.AXE_IRON:
                case World.SHOVEL_IRON:
                    return 5;
                case World.PICK_DIAMOND:
                case World.AXE_DIAMOND:
                case World.SHOVEL_DIAMOND:
                    return 8;
                default:
                    return 1;
            }
        }

        static int getToolBonus(ItemStack s, int blockId) {
            if (s == null) {
                return 0;
            }
            if (isPickaxe(s.id)) {
                if (blockId == World.STONE || blockId == World.COAL || blockId == World.IRON
                        || blockId == World.GOLD || blockId == World.DIAMOND
                        || blockId == World.FURNACE || blockId == World.BG_STONE) {
                    return 4;
                }
            }
            if (isAxe(s.id)) {
                if (blockId == World.WOOD || blockId == World.LEAVES || blockId == World.PLANK
                        || blockId == World.BG_WOOD || blockId == World.BG_PLANK) {
                    return 4;
                }
            }
            if (isShovel(s.id)) {
                if (blockId == World.DIRT || blockId == World.GRASS || blockId == World.SAND
                        || blockId == World.SNOW || blockId == World.BG_DIRT) {
                    return 4;
                }
            }
            return 0;
        }

        static boolean isWrongTool(ItemStack s, int blockId) {
            if (s == null) {
                return false;
            }
            if (isPickaxe(s.id)) {
                return blockId == World.WOOD || blockId == World.LEAVES || blockId == World.PLANK;
            }
            if (isAxe(s.id)) {
                return blockId == World.STONE || blockId == World.COAL || blockId == World.IRON
                        || blockId == World.GOLD || blockId == World.DIAMOND;
            }
            if (isShovel(s.id)) {
                return blockId == World.STONE;
            }
            return false;
        }

        static int getBlockHardness(int blockId) {
            switch (blockId) {
                case World.DIRT:
                case World.GRASS:
                case World.SAND:
                case World.SNOW:
                case World.LEAVES:
                    return 1;
                case World.WOOD:
                case World.PLANK:
                case World.ICE:
                    return 2;
                case World.STONE:
                case World.CHEST:
                    return 3;
                case World.COAL:
                case World.WORKBENCH:
                    return 4;
                case World.IRON:
                case World.FURNACE:
                    return 5;
                case World.GOLD:
                    return 6;
                case World.DIAMOND:
                    return 8;
                case World.GLASS:
                    return 1;
                case World.BOOKSHELF:
                case World.LANTERN:
                case World.LADDER:
                case World.BED:
                case World.SIGN:
                    return 1;
                case World.BG_STONE:
                case World.BG_DIRT:
                case World.BG_WOOD:
                case World.BG_PLANK:
                    return 1;
                case World.DOOR_CLOSED:
                    return 2;
                case World.COMMAND_BLOCK:
                    return 10;
                default:
                    return 2;
            }
        }

        static int getSwordDamage(ItemStack s) {
            if (s == null) {
                return 2;
            }
            switch (s.id) {
                case World.SWORD_WOOD:
                    return 5;
                case World.SWORD_STONE:
                    return 8;
                case World.SWORD_IRON:
                    return 12;
                case World.SWORD_DIAMOND:
                    return 18;
                case World.PICK_WOOD:
                    return 3;
                case World.PICK_STONE:
                    return 4;
                case World.PICK_IRON:
                    return 6;
                case World.PICK_DIAMOND:
                    return 9;
                case World.AXE_WOOD:
                    return 4;
                case World.AXE_STONE:
                    return 6;
                case World.AXE_IRON:
                    return 9;
                case World.AXE_DIAMOND:
                    return 13;
                case World.SHOVEL_WOOD:
                    return 2;
                case World.SHOVEL_STONE:
                    return 3;
                case World.SHOVEL_IRON:
                    return 4;
                case World.SHOVEL_DIAMOND:
                    return 5;
                default:
                    return 2;
            }
        }
        // === НОВОЕ: какие блоки требуют инструмент ===

        static boolean requiresTool(int blockId) {
            switch (blockId) {
                case World.STONE:
                case World.COAL:
                case World.IRON:
                case World.GOLD:
                case World.DIAMOND:
                case World.FURNACE:
                case World.GLASS:
                case World.COMMAND_BLOCK:
                case World.BG_STONE:
                case World.ICE:
                case World.BOOKSHELF:
                case World.CHEST:
                case World.LANTERN:
                    return true;
                default:
                    return false;
            }
        }

        // === НОВОЕ: можно ли добыть этим инструментом ===
        static boolean canHarvest(ItemStack tool, int blockId) {
            if (!requiresTool(blockId)) {
                return true;
            }

            if (isPickaxe(tool == null ? -1 : tool.id)) {
                switch (blockId) {
                    case World.STONE:
                    case World.COAL:
                    case World.IRON:
                    case World.GOLD:
                    case World.DIAMOND:
                    case World.FURNACE:
                    case World.GLASS:
                    case World.BG_STONE:
                    case World.ICE:
                    case World.COMMAND_BLOCK:
                        return true;
                    default:
                        return false;
                }
            }

            if (isAxe(tool == null ? -1 : tool.id)) {
                return blockId == World.BOOKSHELF || blockId == World.CHEST
                        || blockId == World.LANTERN;
            }

            return false;
        }

        // === НОВОЕ: каким инструментом добывается ===
        static String getRequiredTool(int blockId) {
            switch (blockId) {
                case World.STONE:
                case World.COAL:
                case World.IRON:
                case World.GOLD:
                case World.DIAMOND:
                case World.FURNACE:
                case World.GLASS:
                case World.BG_STONE:
                case World.ICE:
                case World.COMMAND_BLOCK:
                    return "кирка";
                case World.BOOKSHELF:
                case World.CHEST:
                case World.LANTERN:
                    return "топор";
                default:
                    return "инструмент";
            }
        }
    }

    // ==================== CRAFTING ====================
    static class Crafting {

        static class Recipe {

            int resultId, resultCount;
            int[][] shape;
            int shapeW, shapeH;
            boolean needsTable;
            String category;
            String hint;

            Recipe(int rId, int rCount, int[][] sh, int w, int h, boolean table, String cat, String hint) {
                resultId = rId;
                resultCount = rCount;
                shape = sh;
                shapeW = w;
                shapeH = h;
                needsTable = table;
                category = cat;
                this.hint = hint;
            }
        }

        private static final List<Recipe> recipes = new ArrayList<>();

        // Пустой слот (бывший "_")
        private static final int E = 0;

        // Хелперы для краткости
        private static int[][] s2(int a, int b, int c, int d) {
            return new int[][]{{a, b}, {c, d}};
        }

        private static int[][] s3(int a, int b, int c, int d, int e, int f, int g, int h, int i) {
            return new int[][]{{a, b, c}, {d, e, f}, {g, h, i}};
        }

        static {
            // ==================== ДОСКИ И ПАЛКИ ====================
            // Доски: 1 дерево (shapeless — в любом углу 2x2)
            recipes.add(new Recipe(World.PLANK, 4, s2(World.WOOD, E, E, E), 2, 2, false, "blocks", "1 дерево → 4 доски"));
            recipes.add(new Recipe(World.PLANK, 4, s2(E, World.WOOD, E, E), 2, 2, false, "blocks", ""));
            recipes.add(new Recipe(World.PLANK, 4, s2(E, E, World.WOOD, E), 2, 2, false, "blocks", ""));
            recipes.add(new Recipe(World.PLANK, 4, s2(E, E, E, World.WOOD), 2, 2, false, "blocks", ""));

            // Палки: 2 доски вертикально
            recipes.add(new Recipe(World.STICK, 4, s2(World.PLANK, E,
                    World.PLANK, E), 2, 2, false, "items", "2 доски → 4 палки"));

            // ==================== БАЗОВЫЙ ДЕКОР ====================
            // Верстак: 4 доски квадратом
            recipes.add(new Recipe(World.WORKBENCH, 1, s2(World.PLANK, World.PLANK,
                    World.PLANK, World.PLANK), 2, 2, false, "decor", "4 доски"));

            // Факел: уголь сверху, палка снизу
            recipes.add(new Recipe(World.TORCH, 4, s2(World.COAL_ITEM, E,
                    World.STICK, E), 2, 2, false, "decor", "уголь + палка"));

            // Сундук: 8 досок вокруг пустого центра (3x3)
            recipes.add(new Recipe(World.CHEST, 1, s3(
                    World.PLANK, World.PLANK, World.PLANK,
                    World.PLANK, E, World.PLANK,
                    World.PLANK, World.PLANK, World.PLANK), 3, 3, true, "decor", "8 досок"));

            // Печь: 8 камней вокруг пустого центра
            recipes.add(new Recipe(World.FURNACE, 1, s3(
                    World.STONE, World.STONE, World.STONE,
                    World.STONE, E, World.STONE,
                    World.STONE, World.STONE, World.STONE), 3, 3, true, "decor", "8 камней"));

            // ==================== ИНСТРУМЕНТЫ: МЕЧИ ====================
            recipes.add(new Recipe(World.SWORD_WOOD, 1, s3(
                    E, World.PLANK, E,
                    E, World.PLANK, E,
                    E, World.STICK, E), 3, 3, true, "tools", "2 доски + палка"));
            recipes.add(new Recipe(World.SWORD_STONE, 1, s3(
                    E, World.STONE, E,
                    E, World.STONE, E,
                    E, World.STICK, E), 3, 3, true, "tools", "2 камня + палка"));
            recipes.add(new Recipe(World.SWORD_IRON, 1, s3(
                    E, World.IRON_INGOT, E,
                    E, World.IRON_INGOT, E,
                    E, World.STICK, E), 3, 3, true, "tools", "2 слитка + палка"));
            recipes.add(new Recipe(World.SWORD_DIAMOND, 1, s3(
                    E, World.DIAMOND_GEM, E,
                    E, World.DIAMOND_GEM, E,
                    E, World.STICK, E), 3, 3, true, "tools", "2 алмаза + палка"));

            // ==================== ИНСТРУМЕНТЫ: КИРКИ ====================
            recipes.add(new Recipe(World.PICK_WOOD, 1, s3(
                    World.PLANK, World.PLANK, World.PLANK,
                    E, World.STICK, E,
                    E, World.STICK, E), 3, 3, true, "tools", "3 доски + 2 палки"));
            recipes.add(new Recipe(World.PICK_STONE, 1, s3(
                    World.STONE, World.STONE, World.STONE,
                    E, World.STICK, E,
                    E, World.STICK, E), 3, 3, true, "tools", "3 камня + 2 палки"));
            recipes.add(new Recipe(World.PICK_IRON, 1, s3(
                    World.IRON_INGOT, World.IRON_INGOT, World.IRON_INGOT,
                    E, World.STICK, E,
                    E, World.STICK, E), 3, 3, true, "tools", "3 слитка + 2 палки"));
            recipes.add(new Recipe(World.PICK_DIAMOND, 1, s3(
                    World.DIAMOND_GEM, World.DIAMOND_GEM, World.DIAMOND_GEM,
                    E, World.STICK, E,
                    E, World.STICK, E), 3, 3, true, "tools", "3 алмаза + 2 палки"));

            // ==================== ИНСТРУМЕНТЫ: ТОПОРЫ ====================
            recipes.add(new Recipe(World.AXE_WOOD, 1, s3(
                    World.PLANK, World.PLANK, E,
                    World.PLANK, World.STICK, E,
                    E, World.STICK, E), 3, 3, true, "tools", "3 доски + 2 палки"));
            recipes.add(new Recipe(World.AXE_STONE, 1, s3(
                    World.STONE, World.STONE, E,
                    World.STONE, World.STICK, E,
                    E, World.STICK, E), 3, 3, true, "tools", "3 камня + 2 палки"));
            recipes.add(new Recipe(World.AXE_IRON, 1, s3(
                    World.IRON_INGOT, World.IRON_INGOT, E,
                    World.IRON_INGOT, World.STICK, E,
                    E, World.STICK, E), 3, 3, true, "tools", "3 слитка + 2 палки"));
            recipes.add(new Recipe(World.AXE_DIAMOND, 1, s3(
                    World.DIAMOND_GEM, World.DIAMOND_GEM, E,
                    World.DIAMOND_GEM, World.STICK, E,
                    E, World.STICK, E), 3, 3, true, "tools", "3 алмаза + 2 палки"));

            // ==================== ИНСТРУМЕНТЫ: ЛОПАТЫ ====================
            recipes.add(new Recipe(World.SHOVEL_WOOD, 1, s3(
                    E, World.PLANK, E,
                    E, World.STICK, E,
                    E, World.STICK, E), 3, 3, true, "tools", "1 доска + 2 палки"));
            recipes.add(new Recipe(World.SHOVEL_STONE, 1, s3(
                    E, World.STONE, E,
                    E, World.STICK, E,
                    E, World.STICK, E), 3, 3, true, "tools", "1 камень + 2 палки"));
            recipes.add(new Recipe(World.SHOVEL_IRON, 1, s3(
                    E, World.IRON_INGOT, E,
                    E, World.STICK, E,
                    E, World.STICK, E), 3, 3, true, "tools", "1 слиток + 2 палки"));
            recipes.add(new Recipe(World.SHOVEL_DIAMOND, 1, s3(
                    E, World.DIAMOND_GEM, E,
                    E, World.STICK, E,
                    E, World.STICK, E), 3, 3, true, "tools", "1 алмаз + 2 палки"));

            // ==================== ЛУК И СТРЕЛЫ ====================
            recipes.add(new Recipe(World.BOW, 1, s3(
                    E, World.STICK, World.LEAVES,
                    World.STICK, E, World.LEAVES,
                    E, World.STICK, World.LEAVES), 3, 3, true, "tools", "3 палки + 3 листвы"));

            recipes.add(new Recipe(World.ARROW, 4, s3(
                    E, E, E,
                    World.COAL_ITEM, World.STICK, World.LEAVES,
                    E, E, E), 3, 3, true, "tools", "уголь + палка + листва"));

            // ==================== ДЕКОР ====================
            // Дверь: 2 колонки по 3 доски
            recipes.add(new Recipe(World.DOOR_CLOSED, 1, s3(
                    World.PLANK, World.PLANK, E,
                    World.PLANK, World.PLANK, E,
                    World.PLANK, World.PLANK, E), 3, 3, true, "decor", "6 досок"));

            // Книжная полка: 6 досок + 3 листвы
            recipes.add(new Recipe(World.BOOKSHELF, 1, s3(
                    World.PLANK, World.PLANK, World.PLANK,
                    World.LEAVES, World.LEAVES, World.LEAVES,
                    World.PLANK, World.PLANK, World.PLANK), 3, 3, true, "decor", "6 досок + 3 листвы"));

            // Лестница: 7 палок буквой П
            recipes.add(new Recipe(World.LADDER, 3, s3(
                    World.STICK, E, World.STICK,
                    World.STICK, World.STICK, World.STICK,
                    World.STICK, E, World.STICK), 3, 3, true, "decor", "7 палок"));

            // Табличка: 6 досок + 1 палка
            recipes.add(new Recipe(World.SIGN, 1, s3(
                    World.PLANK, World.PLANK, World.PLANK,
                    World.PLANK, World.PLANK, World.PLANK,
                    E, World.STICK, E), 3, 3, true, "decor", "6 досок + 1 палка"));

            // Кровать: 3 листвы сверху + 3 доски снизу
            recipes.add(new Recipe(World.BED, 1, s3(
                    World.LEAVES, World.LEAVES, World.LEAVES,
                    World.PLANK, World.PLANK, World.PLANK,
                    E, E, E), 3, 3, true, "decor", "3 доски + 3 листвы"));

            // Фонарь: слиток + факел
            recipes.add(new Recipe(World.LANTERN, 1, s3(
                    E, World.IRON_INGOT, E,
                    E, World.TORCH, E,
                    E, E, E), 3, 3, true, "decor", "слиток + факел"));

            // Командный блок: золото+алмаз+камень
            recipes.add(new Recipe(World.COMMAND_BLOCK, 1, s3(
                    World.STONE, World.GOLD_INGOT, World.STONE,
                    World.GOLD_INGOT, World.DIAMOND_GEM, World.GOLD_INGOT,
                    World.STONE, World.GOLD_INGOT, World.STONE), 3, 3, true, "decor", "4 золота + алмаз + 4 камня"));

            // ==================== ФОНОВЫЕ БЛОКИ ====================
            recipes.add(new Recipe(World.BG_DIRT, 4, s3(
                    World.DIRT, World.DIRT, E,
                    World.DIRT, World.DIRT, E,
                    E, E, E), 3, 3, false, "blocks", "4 грязи"));
            recipes.add(new Recipe(World.BG_STONE, 4, s3(
                    World.STONE, World.STONE, E,
                    World.STONE, World.STONE, E,
                    E, E, E), 3, 3, false, "blocks", "4 камня"));
            recipes.add(new Recipe(World.BG_WOOD, 4, s3(
                    World.WOOD, World.WOOD, E,
                    World.WOOD, World.WOOD, E,
                    E, E, E), 3, 3, false, "blocks", "4 дерева"));
            recipes.add(new Recipe(World.BG_PLANK, 4, s3(
                    World.PLANK, World.PLANK, E,
                    World.PLANK, World.PLANK, E,
                    E, E, E), 3, 3, false, "blocks", "4 доски"));

            // ==================== БРОНЯ: ШЛЕМЫ ====================
            recipes.add(new Recipe(World.HELMET_LEATHER, 1, s3(
                    World.LEAVES, World.LEAVES, World.LEAVES,
                    World.LEAVES, E, World.LEAVES,
                    E, E, E), 3, 3, true, "armor", "5 листвы"));
            recipes.add(new Recipe(World.HELMET_IRON, 1, s3(
                    World.IRON_INGOT, World.IRON_INGOT, World.IRON_INGOT,
                    World.IRON_INGOT, E, World.IRON_INGOT,
                    E, E, E), 3, 3, true, "armor", "5 слитков"));
            recipes.add(new Recipe(World.HELMET_GOLD, 1, s3(
                    World.GOLD_INGOT, World.GOLD_INGOT, World.GOLD_INGOT,
                    World.GOLD_INGOT, E, World.GOLD_INGOT,
                    E, E, E), 3, 3, true, "armor", "5 слитков"));
            recipes.add(new Recipe(World.HELMET_DIAMOND, 1, s3(
                    World.DIAMOND_GEM, World.DIAMOND_GEM, World.DIAMOND_GEM,
                    World.DIAMOND_GEM, E, World.DIAMOND_GEM,
                    E, E, E), 3, 3, true, "armor", "5 алмазов"));

            // ==================== БРОНЯ: НАГРУДНИКИ ====================
            recipes.add(new Recipe(World.CHESTPLATE_LEATHER, 1, s3(
                    World.LEAVES, E, World.LEAVES,
                    World.LEAVES, World.LEAVES, World.LEAVES,
                    World.LEAVES, World.LEAVES, World.LEAVES), 3, 3, true, "armor", "8 листвы"));
            recipes.add(new Recipe(World.CHESTPLATE_IRON, 1, s3(
                    World.IRON_INGOT, E, World.IRON_INGOT,
                    World.IRON_INGOT, World.IRON_INGOT, World.IRON_INGOT,
                    World.IRON_INGOT, World.IRON_INGOT, World.IRON_INGOT), 3, 3, true, "armor", "8 слитков"));
            recipes.add(new Recipe(World.CHESTPLATE_GOLD, 1, s3(
                    World.GOLD_INGOT, E, World.GOLD_INGOT,
                    World.GOLD_INGOT, World.GOLD_INGOT, World.GOLD_INGOT,
                    World.GOLD_INGOT, World.GOLD_INGOT, World.GOLD_INGOT), 3, 3, true, "armor", "8 слитков"));
            recipes.add(new Recipe(World.CHESTPLATE_DIAMOND, 1, s3(
                    World.DIAMOND_GEM, E, World.DIAMOND_GEM,
                    World.DIAMOND_GEM, World.DIAMOND_GEM, World.DIAMOND_GEM,
                    World.DIAMOND_GEM, World.DIAMOND_GEM, World.DIAMOND_GEM), 3, 3, true, "armor", "8 алмазов"));

            // ==================== БРОНЯ: ШТАНЫ ====================
            recipes.add(new Recipe(World.LEGGINGS_LEATHER, 1, s3(
                    World.LEAVES, World.LEAVES, World.LEAVES,
                    World.LEAVES, E, World.LEAVES,
                    World.LEAVES, E, World.LEAVES), 3, 3, true, "armor", "7 листвы"));
            recipes.add(new Recipe(World.LEGGINGS_IRON, 1, s3(
                    World.IRON_INGOT, World.IRON_INGOT, World.IRON_INGOT,
                    World.IRON_INGOT, E, World.IRON_INGOT,
                    World.IRON_INGOT, E, World.IRON_INGOT), 3, 3, true, "armor", "7 слитков"));
            recipes.add(new Recipe(World.LEGGINGS_GOLD, 1, s3(
                    World.GOLD_INGOT, World.GOLD_INGOT, World.GOLD_INGOT,
                    World.GOLD_INGOT, E, World.GOLD_INGOT,
                    World.GOLD_INGOT, E, World.GOLD_INGOT), 3, 3, true, "armor", "7 слитков"));
            recipes.add(new Recipe(World.LEGGINGS_DIAMOND, 1, s3(
                    World.DIAMOND_GEM, World.DIAMOND_GEM, World.DIAMOND_GEM,
                    World.DIAMOND_GEM, E, World.DIAMOND_GEM,
                    World.DIAMOND_GEM, E, World.DIAMOND_GEM), 3, 3, true, "armor", "7 алмазов"));

            // ==================== БРОНЯ: БОТИНКИ ====================
            recipes.add(new Recipe(World.BOOTS_LEATHER, 1, s3(
                    E, E, E,
                    World.LEAVES, E, World.LEAVES,
                    World.LEAVES, E, World.LEAVES), 3, 3, true, "armor", "4 листвы"));
            recipes.add(new Recipe(World.BOOTS_IRON, 1, s3(
                    E, E, E,
                    World.IRON_INGOT, E, World.IRON_INGOT,
                    World.IRON_INGOT, E, World.IRON_INGOT), 3, 3, true, "armor", "4 слитка"));
            recipes.add(new Recipe(World.BOOTS_GOLD, 1, s3(
                    E, E, E,
                    World.GOLD_INGOT, E, World.GOLD_INGOT,
                    World.GOLD_INGOT, E, World.GOLD_INGOT), 3, 3, true, "armor", "4 слитка"));
            recipes.add(new Recipe(World.BOOTS_DIAMOND, 1, s3(
                    E, E, E,
                    World.DIAMOND_GEM, E, World.DIAMOND_GEM,
                    World.DIAMOND_GEM, E, World.DIAMOND_GEM), 3, 3, true, "armor", "4 алмаза"));

            // ==================== ЕДА ====================
            recipes.add(new Recipe(World.BREAD, 1, s3(
                    World.MEAT, World.APPLE, World.APPLE,
                    E, E, E,
                    E, E, E), 3, 3, false, "items", "мясо + 2 яблока"));
        }

        // ==================== ПОИСК РЕЦЕПТА ====================
        static Recipe findRecipe(ItemStack[] grid, boolean hasTable) {
            for (Recipe r : recipes) {
                if (r.needsTable && !hasTable) {
                    continue;
                }
                if (matchesShape(r, grid)) {
                    return r;
                }
            }
            return null;
        }

        private static boolean matchesShape(Recipe r, ItemStack[] grid) {
            int maxOffX = 3 - r.shapeW;
            int maxOffY = 3 - r.shapeH;
            for (int offY = 0; offY <= maxOffY; offY++) {
                for (int offX = 0; offX <= maxOffX; offX++) {
                    if (matchesAt(r, grid, offX, offY)) {
                        return true;
                    }
                }
            }
            return false;
        }

        private static boolean matchesAt(Recipe r, ItemStack[] grid, int offX, int offY) {
            for (int y = 0; y < 3; y++) {
                for (int x = 0; x < 3; x++) {
                    int idx = y * 3 + x;
                    ItemStack stack = grid[idx];
                    int expected = 0;
                    if (y >= offY && y < offY + r.shapeH
                            && x >= offX && x < offX + r.shapeW) {
                        expected = r.shape[y - offY][x - offX];
                    }
                    if (expected == 0) {
                        if (stack != null) {
                            return false;
                        }
                    } else {
                        if (stack == null || stack.id != expected) {
                            return false;
                        }
                    }
                }
            }
            return true;
        }

        static List<Recipe> byCategory(String cat) {
            List<Recipe> list = new ArrayList<>();
            for (Recipe r : recipes) {
                if (r.category.equals(cat)) {
                    list.add(r);
                }
            }
            return list;
        }

        // ==================== РАСХОД ИНГРЕДИЕНТОВ ====================
        // В отличие от старой версии, уменьшаем каждый непустой слот на 1
        static void consumeRecipe(Recipe r, ItemStack[] grid) {
            for (int i = 0; i < grid.length; i++) {
                if (grid[i] != null) {
                    grid[i].count--;
                    if (grid[i].count <= 0) {
                        grid[i] = null;
                    }
                }
            }
        }
    }

    // ==================== TEXTURES (FAITHFUL STYLE) ====================
    static class Textures {

        private static final Map<Integer, BufferedImage> cache = new HashMap<>();
        private static final Map<Integer, String> fileNames = new HashMap<>();
        private static final int TEX_SIZE = 64;
        private static final int PX = 4;

        public static ResourcePack activePack = null;

        static {
            fileNames.put(World.DIRT, "blocks/dirt.png");
            fileNames.put(World.STONE, "blocks/stone.png");
            fileNames.put(World.GRASS, "blocks/grass.png");
            fileNames.put(World.SAND, "blocks/sand.png");
            fileNames.put(World.WOOD, "blocks/wood.png");
            fileNames.put(World.LEAVES, "blocks/leaves.png");
            fileNames.put(World.COAL, "blocks/coal_ore.png");
            fileNames.put(World.IRON, "blocks/iron_ore.png");
            fileNames.put(World.GOLD, "blocks/gold_ore.png");
            fileNames.put(World.DIAMOND, "blocks/diamond_ore.png");
            fileNames.put(World.CHEST, "blocks/chest.png");
            fileNames.put(World.FURNACE, "blocks/furnace.png");
            fileNames.put(World.WORKBENCH, "blocks/workbench.png");
            fileNames.put(World.TORCH, "blocks/torch.png");
            fileNames.put(World.PLANK, "blocks/plank.png");
            fileNames.put(World.SNOW, "blocks/snow.png");
            fileNames.put(World.ICE, "blocks/ice.png");
            fileNames.put(World.DOOR_CLOSED, "blocks/door_closed.png");
            fileNames.put(World.DOOR_OPEN, "blocks/door_open.png");
            fileNames.put(World.GLASS, "blocks/glass.png");
            fileNames.put(World.BOOKSHELF, "blocks/bookshelf.png");
            fileNames.put(World.LANTERN, "blocks/lantern.png");
            fileNames.put(World.LADDER, "blocks/ladder.png");
            fileNames.put(World.BED, "blocks/bed.png");
            fileNames.put(World.SIGN, "blocks/sign.png");
            fileNames.put(World.BG_STONE, "blocks/bg_stone.png");
            fileNames.put(World.BG_DIRT, "blocks/bg_dirt.png");
            fileNames.put(World.BG_WOOD, "blocks/bg_wood.png");
            fileNames.put(World.BG_PLANK, "blocks/bg_plank.png");
            fileNames.put(World.COMMAND_BLOCK, "blocks/command_block.png");
            fileNames.put(World.STICK, "items/stick.png");
            fileNames.put(World.COIN_GOLD, "items/coin_gold.png");
            fileNames.put(World.IRON_INGOT, "items/iron_ingot.png");
            fileNames.put(World.GOLD_INGOT, "items/gold_ingot.png");
            fileNames.put(World.DIAMOND_GEM, "items/diamond_gem.png");
            fileNames.put(World.COAL_ITEM, "items/coal.png");
            fileNames.put(World.ARROW, "items/arrow.png");
            fileNames.put(World.APPLE, "items/apple.png");
            fileNames.put(World.BREAD, "items/bread.png");
            fileNames.put(World.MEAT, "items/meat.png");
            fileNames.put(World.SLIME_BALL, "items/slime_ball.png");
            fileNames.put(World.BOW, "items/bow.png");
            fileNames.put(World.SWORD_WOOD, "items/sword_wood.png");
            fileNames.put(World.SWORD_STONE, "items/sword_stone.png");
            fileNames.put(World.SWORD_IRON, "items/sword_iron.png");
            fileNames.put(World.SWORD_DIAMOND, "items/sword_diamond.png");
            fileNames.put(World.PICK_WOOD, "items/pick_wood.png");
            fileNames.put(World.PICK_STONE, "items/pick_stone.png");
            fileNames.put(World.PICK_IRON, "items/pick_iron.png");
            fileNames.put(World.PICK_DIAMOND, "items/pick_diamond.png");
            fileNames.put(World.AXE_WOOD, "items/axe_wood.png");
            fileNames.put(World.AXE_STONE, "items/axe_stone.png");
            fileNames.put(World.AXE_IRON, "items/axe_iron.png");
            fileNames.put(World.AXE_DIAMOND, "items/axe_diamond.png");
            fileNames.put(World.SHOVEL_WOOD, "items/shovel_wood.png");
            fileNames.put(World.SHOVEL_STONE, "items/shovel_stone.png");
            fileNames.put(World.SHOVEL_IRON, "items/shovel_iron.png");
            fileNames.put(World.SHOVEL_DIAMOND, "items/shovel_diamond.png");
            fileNames.put(World.HELMET_IRON, "items/helmet_iron.png");
            fileNames.put(World.CHESTPLATE_IRON, "items/chest_iron.png");
            fileNames.put(World.LEGGINGS_IRON, "items/legs_iron.png");
            fileNames.put(World.BOOTS_IRON, "items/boots_iron.png");
            fileNames.put(World.HELMET_DIAMOND, "items/helmet_diamond.png");
            fileNames.put(World.CHESTPLATE_DIAMOND, "items/chest_diamond.png");
            fileNames.put(World.LEGGINGS_DIAMOND, "items/legs_diamond.png");
            fileNames.put(World.BOOTS_DIAMOND, "items/boots_diamond.png");
            fileNames.put(World.HELMET_GOLD, "items/helmet_gold.png");
            fileNames.put(World.CHESTPLATE_GOLD, "items/chest_gold.png");
            fileNames.put(World.LEGGINGS_GOLD, "items/legs_gold.png");
            fileNames.put(World.BOOTS_GOLD, "items/boots_gold.png");
            fileNames.put(World.HELMET_LEATHER, "items/helmet_leather.png");
            fileNames.put(World.CHESTPLATE_LEATHER, "items/chest_leather.png");
            fileNames.put(World.LEGGINGS_LEATHER, "items/legs_leather.png");
            fileNames.put(World.BOOTS_LEATHER, "items/boots_leather.png");
        }

        public static BufferedImage get(int block) {
            BufferedImage img = cache.get(block);
            if (img != null) {
                return img;
            }

            String fileName = fileNames.get(block);
            if (fileName != null) {
                String relPath = "textures/" + fileName;
                if (activePack != null && !activePack.isDefault) {
                    img = loadFromPack(activePack, relPath);
                }
                if (img == null) {
                    for (ResourcePack rp : resourcePacks) {
                        if (rp == activePack) {
                            continue;
                        }
                        if (rp.isDefault) {
                            continue;
                        }
                        img = loadFromPack(rp, relPath);
                        if (img != null) {
                            break;
                        }
                    }
                }
                if (img == null) {
                    img = loadDefault(relPath);
                }
            }

            if (img == null) {
                img = generateFallback(block);
            }

            cache.put(block, img);
            return img;
        }

        private static BufferedImage loadFromPack(ResourcePack pack, String rel) {
            if (pack == null) {
                return null;
            }
            try (InputStream is = pack.getResource(rel)) {
                if (is != null) {
                    return ImageIO.read(is);
                }
            } catch (Exception ignored) {
            }
            return null;
        }

        private static BufferedImage loadDefault(String rel) {
            File f = new File("resources/resourcepacks/default/" + rel);
            if (f.exists() && f.isFile()) {
                try {
                    return ImageIO.read(f);
                } catch (Exception ignored) {
                }
            }
            f = new File("resources/" + rel);
            if (f.exists() && f.isFile()) {
                try {
                    return ImageIO.read(f);
                } catch (Exception ignored) {
                }
            }
            try (InputStream is = Textures.class.getResourceAsStream("/resources/resourcepacks/default/" + rel)) {
                if (is != null) {
                    return ImageIO.read(is);
                }
            } catch (Exception ignored) {
            }
            try (InputStream is = Textures.class.getResourceAsStream("/resources/" + rel)) {
                if (is != null) {
                    return ImageIO.read(is);
                }
            } catch (Exception ignored) {
            }
            return null;
        }

        public static void reload() {
            cache.clear();
            PixelFont.reload();
        }

        // === ГЕНЕРАЦИЯ FAITHFUL ===
        private static BufferedImage generateFallback(int block) {
            BufferedImage img = new BufferedImage(TEX_SIZE, TEX_SIZE, BufferedImage.TYPE_INT_ARGB);
            Graphics2D g = img.createGraphics();
            g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_OFF);
            Random rnd = new Random(block * 1000L + 42);

            switch (block) {
                case World.DIRT:
                    drawDirt(g, rnd);
                    break;
                case World.STONE:
                    drawStone(g, rnd);
                    break;
                case World.GRASS:
                    drawGrass(g, rnd);
                    break;
                case World.SAND:
                    drawSand(g, rnd);
                    break;
                case World.WOOD:
                    drawWood(g, rnd);
                    break;
                case World.LEAVES:
                    drawLeaves(g, rnd);
                    break;
                case World.COAL:
                    drawOre(g, new Color(35, 35, 40), new Color(15, 15, 18), new Color(80, 80, 85));
                    break;
                case World.IRON:
                    drawOre(g, new Color(210, 190, 170), new Color(150, 130, 110), new Color(240, 220, 200));
                    break;
                case World.GOLD:
                    drawOre(g, new Color(255, 220, 60), new Color(200, 160, 30), new Color(255, 245, 150));
                    break;
                case World.DIAMOND:
                    drawOre(g, new Color(120, 240, 250), new Color(60, 180, 200), new Color(220, 255, 255));
                    break;
                case World.CHEST:
                    drawChest(g, rnd);
                    break;
                case World.FURNACE:
                    drawFurnace(g, rnd);
                    break;
                case World.WORKBENCH:
                    drawWorkbench(g, rnd);
                    break;
                case World.TORCH:
                    drawTorch(g);
                    break;
                case World.PLANK:
                    drawPlank(g, rnd);
                    break;
                case World.SNOW:
                    drawSnow(g, rnd);
                    break;
                case World.ICE:
                    drawIce(g, rnd);
                    break;
                case World.GLASS:
                    drawGlass(g);
                    break;
                case World.BOOKSHELF:
                    drawBookshelf(g, rnd);
                    break;
                case World.LANTERN:
                    drawLantern(g);
                    break;
                case World.LADDER:
                    drawLadder(g);
                    break;
                case World.BED:
                    drawBed(g);
                    break;
                case World.SIGN:
                    drawSign(g);
                    break;
                case World.BG_STONE:
                    drawBgStone(g, rnd);
                    break;
                case World.BG_DIRT:
                    drawBgDirt(g, rnd);
                    break;
                case World.BG_WOOD:
                    drawBgWood(g, rnd);
                    break;
                case World.BG_PLANK:
                    drawBgPlank(g, rnd);
                    break;
                case World.COMMAND_BLOCK:
                    drawCommandBlock(g, rnd);
                    break;
                case World.STICK:
                    drawStick(g);
                    break;
                case World.COIN_GOLD:
                    drawCoin(g);
                    break;
                case World.IRON_INGOT:
                    drawIngot(g, new Color(210, 210, 220), new Color(150, 150, 165), new Color(250, 250, 255));
                    break;
                case World.GOLD_INGOT:
                    drawIngot(g, new Color(255, 220, 60), new Color(200, 160, 30), new Color(255, 245, 150));
                    break;
                case World.DIAMOND_GEM:
                    drawGem(g);
                    break;
                case World.COAL_ITEM:
                    drawCoal(g);
                    break;
                case World.SLIME_BALL:
                    drawSlimeBall(g);
                    break;
                case World.APPLE:
                    drawApple(g);
                    break;
                case World.BREAD:
                    drawBread(g);
                    break;
                case World.MEAT:
                    drawMeat(g);
                    break;
                case World.ARROW:
                    drawArrow(g);
                    break;
                case World.BOW:
                    drawBow(g);
                    break;
                case World.SWORD_WOOD:
                case World.SWORD_STONE:
                case World.SWORD_IRON:
                case World.SWORD_DIAMOND:
                    drawSword(g, getToolHeadColor(block));
                    break;
                case World.PICK_WOOD:
                case World.PICK_STONE:
                case World.PICK_IRON:
                case World.PICK_DIAMOND:
                    drawPickaxe(g, getToolHeadColor(block));
                    break;
                case World.AXE_WOOD:
                case World.AXE_STONE:
                case World.AXE_IRON:
                case World.AXE_DIAMOND:
                    drawAxe(g, getToolHeadColor(block));
                    break;
                case World.SHOVEL_WOOD:
                case World.SHOVEL_STONE:
                case World.SHOVEL_IRON:
                case World.SHOVEL_DIAMOND:
                    drawShovel(g, getToolHeadColor(block));
                    break;
                case World.HELMET_IRON:
                case World.HELMET_DIAMOND:
                case World.HELMET_GOLD:
                case World.HELMET_LEATHER:
                    drawHelmet(g, getArmorColor(block));
                    break;
                case World.CHESTPLATE_IRON:
                case World.CHESTPLATE_DIAMOND:
                case World.CHESTPLATE_GOLD:
                case World.CHESTPLATE_LEATHER:
                    drawChestplate(g, getArmorColor(block));
                    break;
                case World.LEGGINGS_IRON:
                case World.LEGGINGS_DIAMOND:
                case World.LEGGINGS_GOLD:
                case World.LEGGINGS_LEATHER:
                    drawLeggings(g, getArmorColor(block));
                    break;
                case World.BOOTS_IRON:
                case World.BOOTS_DIAMOND:
                case World.BOOTS_GOLD:
                case World.BOOTS_LEATHER:
                    drawBoots(g, getArmorColor(block));
                    break;
                default:
                    drawStone(g, rnd);
                    break;
            }

            g.dispose();
            return img;
        }

        private static Color getToolHeadColor(int id) {
            switch (id) {
                case World.SWORD_WOOD:
                case World.PICK_WOOD:
                case World.AXE_WOOD:
                case World.SHOVEL_WOOD:
                    return new Color(170, 120, 75);
                case World.SWORD_STONE:
                case World.PICK_STONE:
                case World.AXE_STONE:
                case World.SHOVEL_STONE:
                    return new Color(150, 150, 160);
                case World.SWORD_IRON:
                case World.PICK_IRON:
                case World.AXE_IRON:
                case World.SHOVEL_IRON:
                    return new Color(210, 210, 220);
                case World.SWORD_DIAMOND:
                case World.PICK_DIAMOND:
                case World.AXE_DIAMOND:
                case World.SHOVEL_DIAMOND:
                    return new Color(150, 240, 250);
                default:
                    return Color.GRAY;
            }
        }

        private static Color getArmorColor(int id) {
            if (id == World.HELMET_LEATHER || id == World.CHESTPLATE_LEATHER
                    || id == World.LEGGINGS_LEATHER || id == World.BOOTS_LEATHER) {
                return new Color(160, 110, 70);
            }
            if (id == World.HELMET_IRON || id == World.CHESTPLATE_IRON
                    || id == World.LEGGINGS_IRON || id == World.BOOTS_IRON) {
                return new Color(200, 200, 210);
            }
            if (id == World.HELMET_GOLD || id == World.CHESTPLATE_GOLD
                    || id == World.LEGGINGS_GOLD || id == World.BOOTS_GOLD) {
                return new Color(255, 215, 60);
            }
            if (id == World.HELMET_DIAMOND || id == World.CHESTPLATE_DIAMOND
                    || id == World.LEGGINGS_DIAMOND || id == World.BOOTS_DIAMOND) {
                return new Color(150, 240, 250);
            }
            return Color.GRAY;
        }

        private static void setPx(Graphics2D g, int x, int y, Color c) {
            g.setColor(c);
            g.fillRect(x * PX, y * PX, PX, PX);
        }

        private static Color vary(Color base, Random rnd, int amt) {
            int r = base.getRed() + rnd.nextInt(amt * 2 + 1) - amt;
            int gr = base.getGreen() + rnd.nextInt(amt * 2 + 1) - amt;
            int b = base.getBlue() + rnd.nextInt(amt * 2 + 1) - amt;
            return new Color(clamp(r), clamp(gr), clamp(b));
        }

        private static int clamp(int v) {
            return Math.max(0, Math.min(255, v));
        }

        // === БЛОКИ ===
        // === БЛОКИ ===
        private static void drawDirt(Graphics2D g, Random rnd) {
            for (int y = 0; y < 16; y++) {
                for (int x = 0; x < 16; x++) {
                    int r = 118 + rnd.nextInt(20);
                    int gr = 78 + rnd.nextInt(16);
                    int b = 44 + rnd.nextInt(12);
                    if (rnd.nextInt(12) == 0) {
                        r -= 25;
                        gr -= 20;
                        b -= 10;
                    }
                    if (rnd.nextInt(20) == 0) {
                        r += 25;
                        gr += 20;
                        b += 15;
                    }
                    setPx(g, x, y, new Color(clamp(r), clamp(gr), clamp(b)));
                }
            }
            // Тёмные вкрапления
            for (int i = 0; i < 6; i++) {
                int x = rnd.nextInt(16), y = rnd.nextInt(16);
                setPx(g, x, y, new Color(75, 50, 28));
            }
        }

        private static void drawStone(Graphics2D g, Random rnd) {
            Color base = new Color(128, 128, 136);
            for (int y = 0; y < 16; y++) {
                for (int x = 0; x < 16; x++) {
                    Color c = vary(base, rnd, 12);
                    setPx(g, x, y, c);
                }
            }
            // Трещинки
            g.setColor(new Color(95, 95, 105));
            for (int i = 0; i < 3; i++) {
                int x = rnd.nextInt(14);
                int y = rnd.nextInt(14);
                g.fillRect(x * PX, y * PX, PX, PX / 2);
                g.fillRect((x + 1) * PX, (y + 1) * PX, PX / 2, PX);
            }
            // Блики
            g.setColor(new Color(180, 180, 190, 180));
            for (int i = 0; i < 5; i++) {
                setPx(g, rnd.nextInt(16), rnd.nextInt(16), new Color(170, 170, 180));
            }
        }

        private static void drawGrass(Graphics2D g, Random rnd) {
            // Земля внизу
            for (int y = 5; y < 16; y++) {
                for (int x = 0; x < 16; x++) {
                    int r = 118 + rnd.nextInt(20);
                    int gr = 78 + rnd.nextInt(16);
                    int b = 44 + rnd.nextInt(12);
                    setPx(g, x, y, new Color(clamp(r), clamp(gr), clamp(b)));
                }
            }
            // Трава сверху — с неровным краем
            for (int x = 0; x < 16; x++) {
                int h = 4 + rnd.nextInt(2);
                for (int y = 0; y < h; y++) {
                    float f = y / (float) h;
                    int gr = (int) (175 - f * 55 + rnd.nextInt(20) - 10);
                    int r = (int) (70 + f * 30 + rnd.nextInt(15) - 7);
                    int b = (int) (55 + f * 20 + rnd.nextInt(15) - 7);
                    setPx(g, x, y, new Color(clamp(r), clamp(gr), clamp(b)));
                }
                // Тёмный переход
                if (h < 8) {
                    setPx(g, x, h, new Color(65, 100, 50));
                }
            }
            // Блики на траве
            for (int i = 0; i < 12; i++) {
                int x = rnd.nextInt(16);
                int y = rnd.nextInt(4);
                setPx(g, x, y, new Color(150, 220, 120));
            }
        }

        private static void drawSand(Graphics2D g, Random rnd) {
            for (int y = 0; y < 16; y++) {
                for (int x = 0; x < 16; x++) {
                    int r = 228 + rnd.nextInt(18);
                    int gr = 210 + rnd.nextInt(15);
                    int b = 145 + rnd.nextInt(20);
                    if (rnd.nextInt(15) == 0) {
                        r -= 30;
                        gr -= 25;
                        b -= 20;
                    }
                    setPx(g, x, y, new Color(clamp(r), clamp(gr), clamp(b)));
                }
            }
        }

        private static void drawWood(Graphics2D g, Random rnd) {
            // Кора слева и справа
            for (int x = 0; x < 2; x++) {
                for (int y = 0; y < 16; y++) {
                    int v = 100 + rnd.nextInt(20);
                    setPx(g, x, y, new Color(v, v - 30, v - 55));
                    setPx(g, 15 - x, y, new Color(v, v - 30, v - 55));
                }
            }
            // Внутренние волокна
            for (int x = 2; x < 14; x++) {
                int base = 140 + rnd.nextInt(15);
                for (int y = 0; y < 16; y++) {
                    int v = base + rnd.nextInt(10) - 5;
                    setPx(g, x, y, new Color(v, v - 40, v - 75));
                }
            }
            // Тёмные линии
            g.setColor(new Color(95, 60, 30));
            for (int x = 3; x < 14; x += 3) {
                g.fillRect(x * PX, 0, PX / 2, TEX_SIZE);
            }
        }

        private static void drawLeaves(Graphics2D g, Random rnd) {
            for (int y = 0; y < 16; y++) {
                for (int x = 0; x < 16; x++) {
                    int v = rnd.nextInt(4);
                    int r, gr, b;
                    if (v == 0) {
                        r = 40;
                        gr = 100;
                        b = 35;
                    } else if (v == 1) {
                        r = 65;
                        gr = 145;
                        b = 55;
                    } else if (v == 2) {
                        r = 85;
                        gr = 170;
                        b = 70;
                    } else {
                        r = 110;
                        gr = 195;
                        b = 85;
                    }
                    setPx(g, x, y, new Color(r, gr, b));
                }
            }
        }

        private static void drawOre(Graphics2D g, Color oreColor, Color oreDark, Color oreLight) {
            // Каменная основа
            Random rnd = new Random(0);
            Color base = new Color(128, 128, 136);
            for (int y = 0; y < 16; y++) {
                for (int x = 0; x < 16; x++) {
                    setPx(g, x, y, vary(base, rnd, 12));
                }
            }

            // Крупные пятна руды
            Random r2 = new Random(42);
            int clusters = 3 + r2.nextInt(3);
            for (int i = 0; i < clusters; i++) {
                int cx = 3 + r2.nextInt(10);
                int cy = 3 + r2.nextInt(10);
                int size = 2 + r2.nextInt(2);
                // Основное пятно
                for (int dy = -size; dy <= size; dy++) {
                    for (int dx = -size; dx <= size; dx++) {
                        if (dx * dx + dy * dy > size * size + 1) {
                            continue;
                        }
                        int x = cx + dx, y = cy + dy;
                        if (x < 0 || x > 15 || y < 0 || y > 15) {
                            continue;
                        }
                        setPx(g, x, y, oreColor);
                    }
                }
                // Тёмная обводка
                for (int dy = -size - 1; dy <= size + 1; dy++) {
                    for (int dx = -size - 1; dx <= size + 1; dx++) {
                        int x = cx + dx, y = cy + dy;
                        if (x < 0 || x > 15 || y < 0 || y > 15) {
                            continue;
                        }
                        if (dx * dx + dy * dy <= (size + 1) * (size + 1)
                                && dx * dx + dy * dy > size * size) {
                            if (r2.nextBoolean()) {
                                setPx(g, x, y, oreDark);
                            }
                        }
                    }
                }
                // Блики
                setPx(g, cx, cy - 1, oreLight);
                if (r2.nextBoolean()) {
                    setPx(g, cx + 1, cy, oreLight);
                }
                if (r2.nextBoolean()) {
                    setPx(g, cx, cy, oreLight);
                }
            }
        }

        private static void drawChest(Graphics2D g, Random rnd) {
            Color base = new Color(160, 100, 45);
            for (int y = 0; y < 16; y++) {
                for (int x = 0; x < 16; x++) {
                    setPx(g, x, y, vary(base, rnd, 12));
                }
            }
            // Крышка
            g.setColor(new Color(200, 140, 75));
            g.fillRect(0, 0, TEX_SIZE, 5 * PX);
            g.setColor(new Color(220, 160, 90));
            g.fillRect(0, 0, TEX_SIZE, PX);
            // Обводка
            g.setColor(new Color(80, 50, 20));
            g.fillRect(0, 5 * PX, TEX_SIZE, PX);
            g.fillRect(0, 0, PX, TEX_SIZE);
            g.fillRect(TEX_SIZE - PX, 0, PX, TEX_SIZE);
            g.fillRect(0, TEX_SIZE - PX, TEX_SIZE, PX);
            // Замок
            g.setColor(new Color(255, 220, 80));
            g.fillRect(7 * PX, 5 * PX, 2 * PX, 3 * PX);
            g.setColor(new Color(180, 130, 20));
            g.drawRect(7 * PX, 5 * PX, 2 * PX, 3 * PX);
            // Доски
            g.setColor(new Color(120, 75, 30));
            for (int x = 4; x < 16; x += 4) {
                g.fillRect(x * PX, 6 * PX, PX / 2, 9 * PX);
            }
        }

        private static void drawFurnace(Graphics2D g, Random rnd) {
            Color base = new Color(95, 95, 100);
            for (int y = 0; y < 16; y++) {
                for (int x = 0; x < 16; x++) {
                    setPx(g, x, y, vary(base, rnd, 14));
                }
            }
            // Топка
            g.setColor(new Color(30, 30, 30));
            g.fillRect(4 * PX, 8 * PX, 8 * PX, 6 * PX);
            g.setColor(new Color(15, 15, 15));
            g.drawRect(4 * PX, 8 * PX, 8 * PX, 6 * PX);
            // Огонь
            g.setColor(new Color(255, 90, 20));
            g.fillRect(5 * PX, 11 * PX, 6 * PX, 3 * PX);
            g.setColor(new Color(255, 180, 40));
            g.fillRect(5 * PX, 12 * PX, 6 * PX, 2 * PX);
            g.setColor(new Color(255, 240, 150));
            g.fillRect(6 * PX, 12 * PX, PX, PX);
            g.fillRect(9 * PX, 12 * PX, PX, PX);
            // Верхняя решётка
            g.setColor(new Color(180, 180, 190));
            g.drawRect(4 * PX, 8 * PX, 8 * PX, 6 * PX);
            g.fillRect(4 * PX, 7 * PX, 8 * PX, PX / 2);
        }

        private static void drawWorkbench(Graphics2D g, Random rnd) {
            // Столешница
            for (int x = 0; x < 16; x++) {
                for (int y = 0; y < 3; y++) {
                    setPx(g, x, y, vary(new Color(180, 130, 80), rnd, 12));
                }
            }
            // Тёмная кромка
            g.setColor(new Color(120, 75, 35));
            g.fillRect(0, 3 * PX, TEX_SIZE, PX);
            // Ножки
            for (int y = 4; y < 16; y++) {
                for (int x = 1; x < 4; x++) {
                    setPx(g, x, y, vary(new Color(140, 90, 45), rnd, 10));
                }
                for (int x = 12; x < 15; x++) {
                    setPx(g, x, y, vary(new Color(140, 90, 45), rnd, 10));
                }
            }
            // Инструменты на столе
            g.setColor(new Color(200, 200, 210));
            g.fillRect(6 * PX, PX, 2 * PX, PX);
            g.fillRect(11 * PX, PX, 2 * PX, PX);
            g.setColor(new Color(120, 80, 40));
            g.fillRect(8 * PX, PX, PX, PX);
        }

        private static void drawTorch(Graphics2D g) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            // Палка
            g.setColor(new Color(110, 70, 35));
            g.fillRect(7 * PX, 6 * PX, 2 * PX, 10 * PX);
            g.setColor(new Color(80, 50, 25));
            g.fillRect(7 * PX, 6 * PX, PX, 10 * PX);
            // Огонь
            g.setColor(new Color(255, 140, 40));
            g.fillRect(6 * PX, 3 * PX, 4 * PX, 5 * PX);
            g.setColor(new Color(255, 220, 80));
            g.fillRect(7 * PX, 2 * PX, 2 * PX, 4 * PX);
            g.setColor(new Color(255, 250, 200));
            g.fillRect(7 * PX, 3 * PX, PX, 2 * PX);
        }

        private static void drawPlank(Graphics2D g, Random rnd) {
            Color base = new Color(180, 130, 80);
            for (int y = 0; y < 16; y++) {
                for (int x = 0; x < 16; x++) {
                    setPx(g, x, y, vary(base, rnd, 12));
                }
            }
            // Горизонтальные швы
            g.setColor(new Color(105, 65, 35));
            for (int y = 4; y < 16; y += 4) {
                g.fillRect(0, y * PX, TEX_SIZE, PX / 2);
            }
            // Вертикальные стыки
            g.setColor(new Color(120, 80, 45));
            for (int y = 0; y < 16; y += 4) {
                int offset = (y / 4) % 2 == 0 ? 5 : 11;
                g.fillRect(offset * PX, y * PX, PX / 2, 4 * PX);
            }
        }

        private static void drawSnow(Graphics2D g, Random rnd) {
            for (int y = 0; y < 16; y++) {
                for (int x = 0; x < 16; x++) {
                    int v = 245 + rnd.nextInt(11) - 5;
                    setPx(g, x, y, new Color(clamp(v), clamp(v), 255));
                }
            }
            // Блики
            for (int i = 0; i < 10; i++) {
                setPx(g, rnd.nextInt(16), rnd.nextInt(16), new Color(255, 255, 255));
            }
        }

        private static void drawIce(Graphics2D g, Random rnd) {
            for (int y = 0; y < 16; y++) {
                for (int x = 0; x < 16; x++) {
                    Color c = vary(new Color(150, 200, 245), rnd, 15);
                    setPx(g, x, y, c);
                }
            }
            // Трещины-блики
            g.setColor(new Color(220, 240, 255));
            g.fillRect(2 * PX, 3 * PX, 12 * PX, PX);
            g.fillRect(4 * PX, 8 * PX, 8 * PX, PX);
            g.setColor(new Color(255, 255, 255, 200));
            g.fillRect(3 * PX, 3 * PX, PX, PX);
            g.fillRect(10 * PX, 8 * PX, PX, PX);
        }

        private static void drawGlass(Graphics2D g) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            // Полупрозрачное тело
            g.setColor(new Color(200, 230, 250, 70));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            // Рамка
            g.setColor(new Color(200, 230, 250, 180));
            g.drawRect(0, 0, TEX_SIZE - 1, TEX_SIZE - 1);
            g.drawRect(PX, PX, TEX_SIZE - 2 * PX, TEX_SIZE - 2 * PX);
            // Блики
            g.setColor(new Color(255, 255, 255, 220));
            g.fillRect(PX, PX, PX, PX);
            g.fillRect(TEX_SIZE - 2 * PX, TEX_SIZE - 2 * PX, PX, PX);
            g.fillRect(PX * 3, PX * 2, PX * 2, PX);
        }

        private static void drawBookshelf(Graphics2D g, Random rnd) {
            g.setColor(new Color(140, 95, 55));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            // Полки
            g.setColor(new Color(80, 45, 25));
            for (int i = 0; i < 3; i++) {
                g.fillRect(0, (2 + i * 5) * PX, TEX_SIZE, PX);
            }
            // Книги
            Color[] colors = {
                new Color(200, 60, 60), new Color(60, 120, 200),
                new Color(60, 190, 80), new Color(200, 180, 60),
                new Color(150, 80, 200)
            };
            for (int row = 0; row < 3; row++) {
                int y = row * 5 + 3;
                int x = 0;
                while (x < 16) {
                    int w = 1 + rnd.nextInt(3);
                    if (x + w > 16) {
                        w = 16 - x;
                    }
                    Color c = colors[rnd.nextInt(colors.length)];
                    g.setColor(c);
                    g.fillRect(x * PX, y * PX, w * PX - 1, 4 * PX);
                    g.setColor(c.brighter());
                    g.fillRect(x * PX, y * PX, w * PX - 1, PX / 2);
                    x += w;
                }
            }
        }

        private static void drawLantern(Graphics2D g) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            // Крепление
            g.setColor(new Color(110, 75, 40));
            g.fillRect(7 * PX, 0, 2 * PX, 2 * PX);
            // Корпус
            g.setColor(new Color(255, 200, 70));
            g.fillRect(5 * PX, 3 * PX, 6 * PX, 8 * PX);
            g.setColor(new Color(255, 240, 140));
            g.fillRect(6 * PX, 4 * PX, 4 * PX, 6 * PX);
            g.setColor(new Color(255, 255, 220));
            g.fillRect(7 * PX, 5 * PX, 2 * PX, 3 * PX);
            // Обводка
            g.setColor(new Color(110, 75, 40));
            g.drawRect(5 * PX, 3 * PX, 6 * PX, 8 * PX);
            g.fillRect(5 * PX, 11 * PX, 6 * PX, PX);
            g.fillRect(5 * PX, 2 * PX, 6 * PX, PX);
        }

        private static void drawLadder(Graphics2D g) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            g.setColor(new Color(150, 100, 55));
            g.fillRect(3 * PX, 0, 2 * PX, TEX_SIZE);
            g.fillRect(11 * PX, 0, 2 * PX, TEX_SIZE);
            g.setColor(new Color(120, 80, 45));
            g.fillRect(3 * PX, 0, PX, TEX_SIZE);
            g.fillRect(11 * PX, 0, PX, TEX_SIZE);
            g.setColor(new Color(150, 100, 55));
            for (int i = 2; i < 16; i += 4) {
                g.fillRect(3 * PX, i * PX, 10 * PX, PX);
            }
        }

        private static void drawBed(Graphics2D g) {
            // Основа
            g.setColor(new Color(140, 95, 55));
            g.fillRect(0, 8 * PX, TEX_SIZE, 6 * PX);
            g.setColor(new Color(110, 70, 35));
            g.fillRect(0, 13 * PX, TEX_SIZE, PX);
            // Одеяло
            g.setColor(new Color(200, 60, 60));
            g.fillRect(PX, 6 * PX, TEX_SIZE - 2 * PX, 3 * PX);
            g.setColor(new Color(180, 40, 40));
            g.fillRect(PX, 8 * PX, TEX_SIZE - 2 * PX, PX);
            // Подушка
            g.setColor(new Color(240, 240, 240));
            g.fillRect(3 * PX, 3 * PX, 4 * PX, 4 * PX);
            g.setColor(new Color(220, 220, 220));
            g.fillRect(3 * PX, 6 * PX, 4 * PX, PX);
        }

        private static void drawSign(Graphics2D g) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            // Столб
            g.setColor(new Color(140, 95, 55));
            g.fillRect(7 * PX, 8 * PX, 2 * PX, 8 * PX);
            // Доска
            g.setColor(new Color(180, 130, 80));
            g.fillRect(2 * PX, 3 * PX, 12 * PX, 6 * PX);
            g.setColor(new Color(90, 60, 30));
            g.drawRect(2 * PX, 3 * PX, 12 * PX, 6 * PX);
            // Текст
            g.setColor(new Color(60, 40, 20));
            for (int i = 0; i < 3; i++) {
                g.fillRect(4 * PX, (4 + i) * PX, 8 * PX, PX / 2);
            }
        }

        private static void drawBgStone(Graphics2D g, Random rnd) {
            for (int y = 0; y < 16; y++) {
                for (int x = 0; x < 16; x++) {
                    Color c = vary(new Color(70, 70, 80), rnd, 10);
                    setPx(g, x, y, new Color(c.getRed(), c.getGreen(), c.getBlue(), 190));
                }
            }
        }

        private static void drawBgDirt(Graphics2D g, Random rnd) {
            for (int y = 0; y < 16; y++) {
                for (int x = 0; x < 16; x++) {
                    Color c = vary(new Color(85, 60, 35), rnd, 12);
                    setPx(g, x, y, new Color(c.getRed(), c.getGreen(), c.getBlue(), 190));
                }
            }
        }

        private static void drawBgWood(Graphics2D g, Random rnd) {
            for (int y = 0; y < 16; y++) {
                for (int x = 0; x < 16; x++) {
                    Color c = vary(new Color(100, 70, 40), rnd, 12);
                    setPx(g, x, y, new Color(c.getRed(), c.getGreen(), c.getBlue(), 190));
                }
            }
        }

        private static void drawBgPlank(Graphics2D g, Random rnd) {
            for (int y = 0; y < 16; y++) {
                for (int x = 0; x < 16; x++) {
                    Color c = vary(new Color(130, 95, 60), rnd, 12);
                    setPx(g, x, y, new Color(c.getRed(), c.getGreen(), c.getBlue(), 190));
                }
            }
            g.setColor(new Color(90, 65, 40, 190));
            for (int y = 4; y < 16; y += 4) {
                g.fillRect(0, y * PX, TEX_SIZE, PX / 2);
            }
        }

        private static void drawCommandBlock(Graphics2D g, Random rnd) {
            Color base = new Color(120, 60, 180);
            for (int y = 0; y < 16; y++) {
                for (int x = 0; x < 16; x++) {
                    setPx(g, x, y, vary(base, rnd, 15));
                }
            }
            g.setColor(new Color(70, 30, 120));
            g.drawRect(2 * PX, 2 * PX, 12 * PX, 12 * PX);
            g.setColor(new Color(220, 170, 255));
            g.fillRect(5 * PX, 5 * PX, 6 * PX, 6 * PX);
            g.setColor(new Color(255, 255, 200));
            g.fillRect(7 * PX, 7 * PX, 2 * PX, 2 * PX);
            g.setColor(new Color(255, 255, 255, 180));
            g.fillRect(5 * PX, 5 * PX, 6 * PX, PX);
        }

        // === ПРЕДМЕТЫ ===
        private static void drawStick(Graphics2D g) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            // Толстая палка по диагонали
            g.setColor(new Color(140, 95, 55));
            for (int i = 0; i < 11; i++) {
                int x = 3 + i / 2;
                int y = 12 - i;
                g.fillRect(x * PX, y * PX, PX, PX);
                g.fillRect((x + 1) * PX, y * PX, PX, PX);
            }
            g.setColor(new Color(90, 60, 30));
            for (int i = 0; i < 11; i++) {
                int x = 3 + i / 2;
                int y = 12 - i;
                g.fillRect(x * PX, (y + 1) * PX - PX / 4, PX, PX / 4);
            }
        }

        private static void drawCoin(Graphics2D g) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            for (int y = 0; y < 16; y++) {
                for (int x = 0; x < 16; x++) {
                    int dx = x - 7, dy = y - 7;
                    int d2 = dx * dx + dy * dy;
                    if (d2 <= 36) {
                        Color c = d2 <= 6 ? new Color(255, 250, 180)
                                : d2 <= 18 ? new Color(255, 220, 80)
                                        : d2 <= 30 ? new Color(220, 170, 40)
                                                : new Color(170, 120, 20);
                        setPx(g, x, y, c);
                    }
                }
            }
            // Символ
            g.setColor(new Color(140, 90, 10));
            g.fillRect(6 * PX, 6 * PX, PX * 4, PX);
            g.fillRect(7 * PX, 5 * PX, PX * 2, PX);
            g.fillRect(7 * PX, 8 * PX, PX * 2, PX);
        }

        private static void drawIngot(Graphics2D g, Color base, Color dark, Color light) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            // Трапеция
            g.setColor(dark);
            g.fillRect(2 * PX, 10 * PX, 12 * PX, 2 * PX);
            g.setColor(base);
            g.fillRect(3 * PX, 7 * PX, 10 * PX, 4 * PX);
            g.fillRect(4 * PX, 6 * PX, 8 * PX, PX);
            g.setColor(light);
            g.fillRect(4 * PX, 6 * PX, 8 * PX, PX);
            g.setColor(new Color(255, 255, 255, 200));
            g.fillRect(5 * PX, 6 * PX, PX * 2, PX);
        }

        private static void drawGem(Graphics2D g) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            // Ромб
            int[][] shape = {
                {0, 0, 0, 1, 2, 1, 0, 0, 0},
                {0, 0, 1, 2, 3, 2, 1, 0, 0},
                {0, 1, 2, 3, 3, 3, 2, 1, 0},
                {1, 2, 3, 3, 3, 3, 3, 2, 1},
                {0, 1, 2, 3, 3, 3, 2, 1, 0},
                {0, 0, 1, 2, 3, 2, 1, 0, 0},
                {0, 0, 0, 1, 2, 1, 0, 0, 0}
            };
            for (int y = 0; y < shape.length; y++) {
                for (int x = 0; x < shape[y].length; x++) {
                    int v = shape[y][x];
                    if (v == 0) {
                        continue;
                    }
                    Color c = v == 1 ? new Color(70, 180, 210)
                            : v == 2 ? new Color(150, 240, 250)
                                    : new Color(220, 255, 255);
                    setPx(g, x + 3, y + 4, c);
                }
            }
            // Блик
            g.setColor(new Color(255, 255, 255));
            g.fillRect(7 * PX, 5 * PX, PX, PX);
            g.fillRect(8 * PX, 6 * PX, PX, PX);
        }

        private static void drawCoal(Graphics2D g) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            g.setColor(new Color(35, 35, 40));
            g.fillOval(3 * PX, 4 * PX, 10 * PX, 9 * PX);
            g.setColor(new Color(55, 55, 60));
            g.fillOval(4 * PX, 5 * PX, 6 * PX, 5 * PX);
            g.setColor(new Color(80, 80, 85));
            g.fillRect(5 * PX, 6 * PX, PX, PX);
            g.setColor(new Color(20, 20, 25));
            g.fillOval(3 * PX, 9 * PX, 4 * PX, 3 * PX);
        }

        private static void drawSlimeBall(Graphics2D g) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            g.setColor(new Color(120, 210, 120));
            g.fillOval(3 * PX, 4 * PX, 10 * PX, 10 * PX);
            g.setColor(new Color(170, 245, 170));
            g.fillOval(5 * PX, 6 * PX, 3 * PX, 3 * PX);
            g.setColor(new Color(80, 170, 80));
            g.fillOval(4 * PX, 10 * PX, 2 * PX, 2 * PX);
            g.fillOval(9 * PX, 8 * PX, 2 * PX, 2 * PX);
        }

        private static void drawApple(Graphics2D g) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            g.setColor(new Color(220, 40, 40));
            g.fillOval(3 * PX, 4 * PX, 10 * PX, 10 * PX);
            g.setColor(new Color(180, 20, 20));
            g.fillOval(4 * PX, 10 * PX, 8 * PX, 4 * PX);
            g.setColor(new Color(255, 100, 100));
            g.fillOval(5 * PX, 5 * PX, 3 * PX, 3 * PX);
            // Черенок
            g.setColor(new Color(90, 60, 30));
            g.fillRect(7 * PX, PX, PX, 3 * PX);
            g.setColor(new Color(80, 170, 60));
            g.fillRect(8 * PX, PX, 2 * PX, PX);
        }

        private static void drawBread(Graphics2D g) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            g.setColor(new Color(200, 150, 80));
            g.fillOval(2 * PX, 6 * PX, 12 * PX, 7 * PX);
            g.setColor(new Color(230, 190, 120));
            g.fillOval(4 * PX, 7 * PX, 8 * PX, 3 * PX);
            g.setColor(new Color(150, 110, 50));
            g.drawOval(2 * PX, 6 * PX, 12 * PX, 7 * PX);
            // Надрезы
            g.setColor(new Color(160, 110, 50));
            g.fillRect(5 * PX, 8 * PX, PX * 6, PX / 2);
        }

        private static void drawMeat(Graphics2D g) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            g.setColor(new Color(200, 100, 90));
            g.fillOval(3 * PX, 5 * PX, 10 * PX, 8 * PX);
            g.setColor(new Color(230, 140, 130));
            g.fillOval(5 * PX, 6 * PX, 4 * PX, 3 * PX);
            // Кость
            g.setColor(new Color(240, 240, 220));
            g.fillRect(2 * PX, 9 * PX, 3 * PX, 2 * PX);
            g.fillRect(PX, 8 * PX, 2 * PX, 3 * PX);
        }

        private static void drawArrow(Graphics2D g) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            // Древко
            g.setColor(new Color(140, 95, 55));
            for (int i = 0; i < 10; i++) {
                g.fillRect((5 + i / 2) * PX, (12 - i) * PX, PX, PX);
                g.fillRect((5 + i / 2) * PX, (12 - i) * PX, PX, PX / 2);
            }
            // Наконечник
            g.setColor(new Color(200, 200, 210));
            g.fillRect(11 * PX, 2 * PX, PX, PX);
            g.fillRect(12 * PX, PX, PX, PX);
            g.fillRect(11 * PX, PX, PX, PX);
            // Оперение
            g.setColor(new Color(240, 240, 240));
            g.fillRect(3 * PX, 11 * PX, PX * 2, PX);
            g.fillRect(4 * PX, 12 * PX, PX * 2, PX);
        }

        private static void drawBow(Graphics2D g) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            // Дуга
            g.setColor(new Color(140, 95, 55));
            for (int i = 0; i < 12; i++) {
                int x = 3 + Math.abs(6 - i) / 2;
                int y = i + 2;
                g.fillRect(x * PX, y * PX, PX * 2, PX);
            }
            // Тетива
            g.setColor(new Color(240, 240, 240));
            g.drawLine(3 * PX, 3 * PX, 3 * PX, 14 * PX);
        }

        private static void drawSword(Graphics2D g, Color head) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            // Рукоятка
            g.setColor(new Color(100, 65, 35));
            g.fillRect(3 * PX, 12 * PX, 4 * PX, 3 * PX);
            g.setColor(new Color(70, 45, 20));
            g.fillRect(3 * PX, 12 * PX, PX, 3 * PX);
            g.fillRect(6 * PX, 12 * PX, PX, 3 * PX);
            // Гарда
            g.setColor(new Color(80, 50, 25));
            g.fillRect(2 * PX, 10 * PX, 6 * PX, 2 * PX);
            // Клинок
            g.setColor(head);
            for (int i = 0; i < 9; i++) {
                g.fillRect((7 - i / 2) * PX, (9 - i) * PX, PX, PX);
                g.fillRect((7 - i / 2) * PX, (9 - i) * PX, PX, PX);
            }
            g.setColor(head.brighter());
            g.fillRect(6 * PX, PX, PX, 2 * PX);
            g.fillRect(9 * PX, PX, PX, 2 * PX);
        }

        private static void drawPickaxe(Graphics2D g, Color head) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            // Рукоятка
            g.setColor(new Color(100, 65, 35));
            for (int i = 0; i < 10; i++) {
                g.fillRect((5 + i / 2) * PX, (13 - i) * PX, PX, PX);
                g.fillRect((6 + i / 2) * PX, (13 - i) * PX, PX, PX);
            }
            // Головка
            g.setColor(head);
            g.fillRect(3 * PX, 2 * PX, PX * 8, PX);
            g.fillRect(2 * PX, 3 * PX, PX, PX);
            g.fillRect(12 * PX, 3 * PX, PX, PX);
            g.fillRect(7 * PX, PX, PX * 2, PX);
            g.setColor(head.brighter());
            g.fillRect(4 * PX, 2 * PX, PX * 6, PX / 2);
        }

        private static void drawAxe(Graphics2D g, Color head) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            // Рукоятка
            g.setColor(new Color(100, 65, 35));
            for (int i = 0; i < 10; i++) {
                g.fillRect((5 + i / 2) * PX, (13 - i) * PX, PX, PX);
                g.fillRect((6 + i / 2) * PX, (13 - i) * PX, PX, PX);
            }
            // Лезвие
            g.setColor(head);
            g.fillRect(6 * PX, 2 * PX, 6 * PX, 4 * PX);
            g.fillRect(8 * PX, 6 * PX, 4 * PX, PX);
            g.setColor(head.brighter());
            g.fillRect(7 * PX, 3 * PX, 4 * PX, 2 * PX);
            g.setColor(head.darker());
            g.drawRect(6 * PX, 2 * PX, 6 * PX, 4 * PX);
        }

        private static void drawShovel(Graphics2D g, Color head) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            // Рукоятка
            g.setColor(new Color(100, 65, 35));
            for (int i = 0; i < 10; i++) {
                g.fillRect((5 + i / 2) * PX, (13 - i) * PX, PX, PX);
            }
            // Лопатка
            g.setColor(head);
            g.fillRect(6 * PX, 2 * PX, 5 * PX, 5 * PX);
            g.setColor(head.brighter());
            g.fillRect(7 * PX, 3 * PX, 3 * PX, 2 * PX);
            g.setColor(head.darker());
            g.drawRect(6 * PX, 2 * PX, 5 * PX, 5 * PX);
        }

        // === БРОНЯ ===
        private static void drawHelmet(Graphics2D g, Color color) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            g.setColor(color);
            g.fillRect(4 * PX, 4 * PX, 8 * PX, 6 * PX);
            g.fillRect(3 * PX, 5 * PX, PX, 4 * PX);
            g.fillRect(12 * PX, 5 * PX, PX, 4 * PX);
            g.setColor(color.darker());
            g.fillRect(4 * PX, 8 * PX, 8 * PX, 2 * PX);
            g.setColor(color.brighter());
            g.fillRect(5 * PX, 4 * PX, 6 * PX, PX);
        }

        private static void drawChestplate(Graphics2D g, Color color) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            g.setColor(color);
            g.fillRect(4 * PX, 4 * PX, 8 * PX, 8 * PX);
            g.setColor(color.darker());
            g.fillRect(7 * PX, 4 * PX, 2 * PX, 8 * PX);
            g.setColor(color.brighter());
            g.fillRect(4 * PX, 4 * PX, 8 * PX, PX);
        }

        private static void drawLeggings(Graphics2D g, Color color) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            g.setColor(color);
            g.fillRect(5 * PX, 5 * PX, 6 * PX, 3 * PX);
            g.fillRect(4 * PX, 8 * PX, 3 * PX, 5 * PX);
            g.fillRect(9 * PX, 8 * PX, 3 * PX, 5 * PX);
        }

        private static void drawBoots(Graphics2D g, Color color) {
            g.setColor(new Color(0, 0, 0, 0));
            g.fillRect(0, 0, TEX_SIZE, TEX_SIZE);
            g.setColor(color);
            g.fillRect(4 * PX, 8 * PX, 3 * PX, 5 * PX);
            g.fillRect(9 * PX, 8 * PX, 3 * PX, 5 * PX);
            g.fillRect(3 * PX, 12 * PX, 4 * PX, PX);
            g.fillRect(9 * PX, 12 * PX, 4 * PX, PX);
        }
    }

    // ==================== WORLD ====================
    static class World implements Serializable {

        private static final long serialVersionUID = 12L;

        public static final int AIR = 0;
        public static final int DIRT = 1;
        public static final int STONE = 2;
        public static final int GRASS = 3;
        public static final int SAND = 4;
        public static final int WOOD = 5;
        public static final int LEAVES = 6;
        public static final int COAL = 7;
        public static final int IRON = 8;
        public static final int GOLD = 9;
        public static final int DIAMOND = 10;
        public static final int CHEST = 11;
        public static final int FURNACE = 12;
        public static final int WORKBENCH = 13;
        public static final int TORCH = 14;
        public static final int IRON_INGOT = 15;
        public static final int GOLD_INGOT = 16;
        public static final int DIAMOND_GEM = 17;
        public static final int COAL_ITEM = 18;
        public static final int PLANK = 19;
        public static final int DOOR = 20;
        public static final int COIN_GOLD = 21;
        public static final int SNOW = 22;
        public static final int ICE = 23;
        public static final int SWORD_WOOD = 24;
        public static final int SWORD_STONE = 25;
        public static final int SWORD_IRON = 26;
        public static final int SWORD_DIAMOND = 27;
        public static final int PICK_WOOD = 28;
        public static final int PICK_STONE = 29;
        public static final int PICK_IRON = 30;
        public static final int PICK_DIAMOND = 31;
        public static final int AXE_WOOD = 32;
        public static final int AXE_STONE = 33;
        public static final int AXE_IRON = 34;
        public static final int AXE_DIAMOND = 35;
        public static final int DOOR_CLOSED = 36;
        public static final int DOOR_OPEN = 37;
        public static final int BG_STONE = 38;
        public static final int BG_DIRT = 39;
        public static final int BG_WOOD = 40;
        public static final int BG_PLANK = 41;
        public static final int CRAFT_TABLE = 42;
        public static final int BOOKSHELF = 50;
        public static final int GLASS = 51;
        public static final int LANTERN = 52;
        public static final int LADDER = 53;
        public static final int BED = 54;
        public static final int SIGN = 55;
        public static final int SHOVEL_WOOD = 60;
        public static final int SHOVEL_STONE = 61;
        public static final int SHOVEL_IRON = 62;
        public static final int SHOVEL_DIAMOND = 63;
        public static final int BOW = 70;
        public static final int ARROW = 71;
        public static final int HELMET_IRON = 80;
        public static final int CHESTPLATE_IRON = 81;
        public static final int LEGGINGS_IRON = 82;
        public static final int BOOTS_IRON = 83;
        public static final int HELMET_DIAMOND = 84;
        public static final int CHESTPLATE_DIAMOND = 85;
        public static final int LEGGINGS_DIAMOND = 86;
        public static final int BOOTS_DIAMOND = 87;
        public static final int HELMET_GOLD = 88;
        public static final int CHESTPLATE_GOLD = 89;
        public static final int LEGGINGS_GOLD = 90;
        public static final int BOOTS_GOLD = 91;
        public static final int HELMET_LEATHER = 92;
        public static final int CHESTPLATE_LEATHER = 93;
        public static final int LEGGINGS_LEATHER = 94;
        public static final int BOOTS_LEATHER = 95;
        public static final int COMMAND_BLOCK = 100;
        public static final int APPLE = 110;
        public static final int BREAD = 111;
        public static final int MEAT = 112;
        public static final int SLIME_BALL = 113;
        public static final int STICK = 120;

        private final int width, height;
        private final int[][] tiles;
        private final int[][] background;
        public String name = "world";
        public long seed = 0;
        public WorldType worldType = WorldType.NORMAL;
        public GameMode mode = GameMode.SURVIVAL;
        public final List<WorkBlock> workBlocks = new ArrayList<>();
        public final List<Integer> villageX = new ArrayList<>();
        public final List<Integer> villageY = new ArrayList<>();
        public final List<CommandBlockData> commandBlocks = new ArrayList<>();
        public final List<ChestLoot> chestLoot = new ArrayList<>();

        public World(int width, int height, long seed, WorldType type,
                double oreDensity, double treeDensity,
                boolean structures, Difficulty difficulty) {
            this.width = width;
            this.height = height;
            this.tiles = new int[width][height];
            this.background = new int[width][height];
            this.seed = seed;
            this.worldType = type;
            if (width > 10) {
                generate(seed, oreDensity, treeDensity, structures, difficulty);
            }
        }

        public World(int width, int height, long seed) {
            this(width, height, seed, WorldType.NORMAL, 1.0, 1.0, true, Difficulty.NORMAL);
        }

        private void generate(long seed, double oreDensity, double treeDensity,
                boolean structures, Difficulty difficulty) {
            Random rnd = new Random(seed);

            int baseY = height / 3;
            double ampScale = 1.0;
            int surfaceType = GRASS;
            int dirtType = DIRT;
            int stoneType = STONE;
            int airAbove = AIR;
            boolean hasCaves = true;
            boolean hasTrees = true;

            switch (worldType) {
                case NETHER:
                    baseY = height / 2;
                    ampScale = 0.6;
                    surfaceType = COAL;
                    dirtType = COAL;
                    hasTrees = false;
                    break;
                case HEAVEN:
                    baseY = height / 3;
                    ampScale = 1.5;
                    hasCaves = false;
                    break;
                case CAVE:
                    baseY = height / 3;
                    surfaceType = STONE;
                    dirtType = STONE;
                    hasTrees = false;
                    break;
                case OCEAN:
                    baseY = height / 2;
                    ampScale = 0.3;
                    surfaceType = SAND;
                    dirtType = SAND;
                    hasTrees = false;
                    break;
                case WASTELAND:
                    baseY = height / 3;
                    surfaceType = SAND;
                    dirtType = SAND;
                    hasTrees = false;
                    break;
                case SNOWY:
                    surfaceType = SNOW;
                    break;
                case FLAT:
                    baseY = height / 2;
                    ampScale = 0.0;
                    hasCaves = false;
                    hasTrees = false;
                    break;
            }

            double[] surface = new double[width];
            int octaves = 5;
            double[] freqs = new double[octaves];
            double[] amps = new double[octaves];
            double[] phases = new double[octaves];
            for (int i = 0; i < octaves; i++) {
                freqs[i] = Math.pow(2, i) * 0.006;
                amps[i] = 18.0 / (i + 1) * ampScale;
                phases[i] = rnd.nextDouble() * Math.PI * 2;
            }
            for (int x = 0; x < width; x++) {
                double h = 0;
                for (int i = 0; i < octaves; i++) {
                    h += Math.sin(x * freqs[i] + phases[i]) * amps[i];
                }
                h += (rnd.nextDouble() - 0.5) * 1.5;
                surface[x] = baseY + h;
            }
            for (int pass = 0; pass < 3; pass++) {
                double[] s2 = surface.clone();
                for (int x = 1; x < width - 1; x++) {
                    s2[x] = (surface[x - 1] + surface[x] * 2 + surface[x + 1]) / 4.0;
                }
                surface = s2;
            }

            int[] biome = new int[width];
            int biomeLen = 0;
            int currentBiome = rnd.nextInt(3);
            for (int x = 0; x < width; x++) {
                if (biomeLen <= 0) {
                    currentBiome = rnd.nextInt(3);
                    biomeLen = 40 + rnd.nextInt(60);
                }
                biome[x] = currentBiome;
                biomeLen--;
            }

            for (int x = 0; x < width; x++) {
                int top = (int) surface[x];
                top = Math.max(10, Math.min(height - 30, top));
                surface[x] = top;
                int surf = surfaceType;
                int dirt = dirtType;
                if (worldType == WorldType.NORMAL || worldType == WorldType.JUNGLE) {
                    if (biome[x] == 1) {
                        surf = SAND;
                    } else if (biome[x] == 2) {
                        surf = SNOW;
                    }
                }
                int dirtDepth = 4 + rnd.nextInt(3);
                for (int y = 0; y < height; y++) {
                    if (y < top) {
                        tiles[x][y] = airAbove;
                    } else if (y == top) {
                        tiles[x][y] = surf;
                    } else if (y < top + dirtDepth) {
                        tiles[x][y] = dirt;
                    } else {
                        tiles[x][y] = stoneType;
                    }
                }
            }

            if (Modules.AUTO_GEN_BG) {
                for (int x = 0; x < width; x++) {
                    int top = (int) surface[x];
                    for (int y = top; y < height; y++) {
                        if (tiles[x][y] == AIR) {
                            if (y < top + 6) {
                                background[x][y] = BG_DIRT;
                            } else {
                                background[x][y] = BG_STONE;
                            }
                        }
                    }
                }
            }

            if (hasCaves) {
                int numCaves = (int) ((15 + rnd.nextInt(20)) * (worldType == WorldType.CAVE ? 3 : 1));
                for (int i = 0; i < numCaves; i++) {
                    int startX = rnd.nextInt(width);
                    int startY = (int) (height * (0.35 + rnd.nextDouble() * 0.55));
                    int length = (int) ((50 + rnd.nextInt(180)) * (worldType == WorldType.CAVE ? 2 : 1));
                    int radius = 3 + rnd.nextInt(5);
                    carveWorm(startX, startY, length, radius, rnd);
                }
            }

            for (int x = 0; x < width; x++) {
                for (int y = 0; y < height; y++) {
                    if (tiles[x][y] != STONE) {
                        continue;
                    }
                    int depth = y - (int) surface[x];
                    double roll = rnd.nextDouble() / Math.max(0.1, oreDensity);
                    if (roll < 0.015) {
                        tiles[x][y] = COAL;
                        continue;
                    }
                    if (depth > 6 && roll < 0.028) {
                        tiles[x][y] = IRON;
                        continue;
                    }
                    if (depth > 18 && roll < 0.034) {
                        tiles[x][y] = GOLD;
                        continue;
                    }
                    if (depth > 30 && roll < 0.036) {
                        tiles[x][y] = DIAMOND;
                        continue;
                    }
                }
            }

            if (hasTrees && treeDensity > 0) {
                for (int x = 4; x < width - 4; x++) {
                    if (rnd.nextDouble() > 0.07 * treeDensity) {
                        continue;
                    }
                    int top = (int) surface[x];
                    if (top < 5 || top > height - 10) {
                        continue;
                    }
                    int g = tiles[x][top];
                    if (g != GRASS && g != SNOW && g != SAND) {
                        continue;
                    }
                    int h = 5 + rnd.nextInt(4);
                    for (int i = 1; i <= h; i++) {
                        if (inBounds(x, top - i)) {
                            tiles[x][top - i] = WOOD;
                        }
                    }
                    int leafTop = top - h;
                    for (int dy = -2; dy <= 1; dy++) {
                        for (int dx = -2; dx <= 2; dx++) {
                            if (dx == 0 && dy == 0) {
                                continue;
                            }
                            if (Math.abs(dx) + Math.abs(dy) > 3) {
                                continue;
                            }
                            int tx = x + dx, ty = leafTop + dy;
                            if (inBounds(tx, ty) && tiles[tx][ty] == AIR) {
                                tiles[tx][ty] = LEAVES;
                            }
                        }
                    }
                }
            }

            for (int x = 4; x < width - 4; x++) {
                if (biome[x] != 1) {
                    continue;
                }
                if (rnd.nextDouble() < 0.03) {
                    int top = (int) surface[x];
                    if (tiles[x][top] != SAND) {
                        continue;
                    }
                    int h = 2 + rnd.nextInt(3);
                    for (int i = 1; i <= h; i++) {
                        if (inBounds(x, top - i)) {
                            tiles[x][top - i] = WOOD;
                        }
                    }
                }
            }

            if (structures) {
                int numVillages = 1 + rnd.nextInt(3);
                for (int v = 0; v < numVillages; v++) {
                    int vx = 80 + rnd.nextInt(Math.max(1, width - 160));
                    int vy = (int) surface[vx];
                    if (vy < 20 || vy > height - 30) {
                        continue;
                    }
                    buildVillage(vx, vy, rnd);
                }
            }
        }

        private void carveWorm(int cx, int cy, int length, int radius, Random rnd) {
            double angle = rnd.nextDouble() * Math.PI * 2;
            for (int step = 0; step < length; step++) {
                angle += (rnd.nextDouble() - 0.5) * 0.5;
                cx += (int) (Math.cos(angle) * 1.5);
                cy += (int) (Math.sin(angle) * 1.5);
                int r = radius - step * radius / (length + 1) / 4;
                if (r < 1) {
                    r = 1;
                }
                for (int dx = -r; dx <= r; dx++) {
                    for (int dy = -r; dy <= r; dy++) {
                        if (dx * dx + dy * dy > r * r) {
                            continue;
                        }
                        int tx = cx + dx, ty = cy + dy;
                        if (!inBounds(tx, ty)) {
                            continue;
                        }
                        int b = tiles[tx][ty];
                        if (b == STONE || b == DIRT || b == GRASS || b == SAND
                                || b == SNOW || b == ICE || b == COAL || b == IRON
                                || b == GOLD || b == DIAMOND) {
                            tiles[tx][ty] = AIR;
                        }
                    }
                }
            }
        }

        private void buildVillage(int cx, int cy, Random rnd) {
            int numHouses = 3 + rnd.nextInt(3);
            List<int[]> housePositions = new ArrayList<>();
            for (int i = 0; i < numHouses; i++) {
                int hx = cx + (i - numHouses / 2) * 14 + rnd.nextInt(6) - 3;
                if (hx < 10 || hx > width - 10) {
                    continue;
                }
                int hy = findSurface(hx);
                if (Math.abs(hy - cy) > 6) {
                    hy = cy;
                }
                housePositions.add(new int[]{hx, hy});
            }
            for (int i = 0; i < housePositions.size() - 1; i++) {
                int[] a = housePositions.get(i);
                int[] b = housePositions.get(i + 1);
                int y = Math.min(a[1], b[1]);
                for (int x = Math.min(a[0], b[0]); x <= Math.max(a[0], b[0]); x++) {
                    if (inBounds(x, y)) {
                        tiles[x][y] = PLANK;
                    }
                }
            }
            for (int[] pos : housePositions) {
                buildHouse(pos[0], pos[1], rnd);
                villageX.add(pos[0]);
                villageY.add(pos[1] - 1);
            }
        }

        private void buildHouse(int cx, int cy, Random rnd) {
            int w = 7 + rnd.nextInt(3);
            int h = 5 + rnd.nextInt(2);
            for (int x = -w / 2 - 1; x <= w / 2 + 1; x++) {
                for (int y = 0; y < h + 3; y++) {
                    int tx = cx + x, ty = cy - y;
                    if (inBounds(tx, ty) && y > 0) {
                        tiles[tx][ty] = AIR;
                    }
                }
            }
            for (int x = -w / 2; x <= w / 2; x++) {
                for (int y = 0; y < h; y++) {
                    int tx = cx + x, ty = cy - y;
                    if (!inBounds(tx, ty)) {
                        continue;
                    }
                    if (y == 0) {
                        tiles[tx][ty] = PLANK;
                    } else if (y == h - 1) {
                        tiles[tx][ty] = PLANK;
                    } else if (x == -w / 2 || x == w / 2) {
                        tiles[tx][ty] = PLANK;
                    } else if (y == h - 2 && (x == -w / 2 + 1 || x == w / 2 - 1)) {
                        tiles[tx][ty] = BG_PLANK;
                    } else if (y == 1 && (x == -2 || x == 2)) {
                        tiles[tx][ty] = TORCH;
                    } else {
                        tiles[tx][ty] = AIR;
                    }
                }
            }
            int doorX = cx + (rnd.nextBoolean() ? -w / 2 : w / 2);
            int doorY = cy - 1;
            if (inBounds(doorX, doorY)) {
                tiles[doorX][doorY] = DOOR_CLOSED;
                if (inBounds(doorX, doorY - 1)) {
                    tiles[doorX][doorY - 1] = DOOR_CLOSED;
                }
            }
            int chestX = cx + rnd.nextInt(w - 2) - (w - 2) / 2;
            int chestY = cy - 1;
            if (inBounds(chestX, chestY) && tiles[chestX][chestY] == AIR) {
                tiles[chestX][chestY] = CHEST;
            }
            int tableX = cx + rnd.nextInt(w - 2) - (w - 2) / 2;
            int tableY = cy - 1;
            if (inBounds(tableX, tableY) && tiles[tableX][tableY] == AIR) {
                tiles[tableX][tableY] = WORKBENCH;
            }
        }

        public void tick() {
            for (int x = 0; x < width; x++) {
                for (int y = height - 2; y >= 0; y--) {
                    if (tiles[x][y] == SAND && tiles[x][y + 1] == AIR) {
                        tiles[x][y + 1] = SAND;
                        tiles[x][y] = AIR;
                    }
                }
            }
        }

        public int findSurface(int x) {
            if (x < 0 || x >= width) {
                return height / 3;
            }
            for (int y = 0; y < height; y++) {
                if (tiles[x][y] != AIR) {
                    return y;
                }
            }
            return height / 3;
        }

        public boolean inBounds(int x, int y) {
            return x >= 0 && y >= 0 && x < width && y < height;
        }

        public int getBlock(int x, int y) {
            if (!inBounds(x, y)) {
                return STONE;
            }
            return tiles[x][y];
        }

        public void setBlock(int x, int y, int b) {
            if (inBounds(x, y)) {
                tiles[x][y] = b;

            }
        }

        public int getBackground(int x, int y) {
            if (!inBounds(x, y)) {
                return AIR;
            }
            return background[x][y];
        }

        public void setBackground(int x, int y, int b) {
            if (inBounds(x, y)) {
                background[x][y] = b;

            }
        }

        public boolean isSolid(int x, int y) {
            int b = getBlock(x, y);
            if (b == AIR || b == TORCH || b == DOOR_OPEN) {
                return false;
            }
            if (b >= BG_STONE && b <= BG_PLANK) {
                return false;
            }
            if (b == LADDER || b == STICK) {
                return false;
            }
            return true;
        }

        public int getWidth() {
            return width;
        }

        public int getHeight() {
            return height;
        }

        public static String blockName(int b) {
            switch (b) {
                case DIRT:
                    return "Грязь";
                case STONE:
                    return "Камень";
                case GRASS:
                    return "Трава";
                case SAND:
                    return "Песок";
                case WOOD:
                    return "Дерево";
                case LEAVES:
                    return "Листва";
                case COAL:
                    return "Угольная руда";
                case IRON:
                    return "Железная руда";
                case GOLD:
                    return "Золотая руда";
                case DIAMOND:
                    return "Алмазная руда";
                case CHEST:
                    return "Сундук";
                case FURNACE:
                    return "Печь";
                case WORKBENCH:
                    return "Верстак";
                case TORCH:
                    return "Факел";
                case IRON_INGOT:
                    return "Железный слиток";
                case GOLD_INGOT:
                    return "Золотой слиток";
                case DIAMOND_GEM:
                    return "Алмаз";
                case COAL_ITEM:
                    return "Уголь";
                case PLANK:
                    return "Доски";
                case DOOR:
                    return "Дверь";
                case COIN_GOLD:
                    return "Золотая монета";
                case SNOW:
                    return "Снег";
                case ICE:
                    return "Лёд";
                case SWORD_WOOD:
                    return "Деревянный меч";
                case SWORD_STONE:
                    return "Каменный меч";
                case SWORD_IRON:
                    return "Железный меч";
                case SWORD_DIAMOND:
                    return "Алмазный меч";
                case PICK_WOOD:
                    return "Деревянная кирка";
                case PICK_STONE:
                    return "Каменная кирка";
                case PICK_IRON:
                    return "Железная кирка";
                case PICK_DIAMOND:
                    return "Алмазная кирка";
                case AXE_WOOD:
                    return "Деревянный топор";
                case AXE_STONE:
                    return "Каменный топор";
                case AXE_IRON:
                    return "Железный топор";
                case AXE_DIAMOND:
                    return "Алмазный топор";
                case SHOVEL_WOOD:
                    return "Деревянная лопата";
                case SHOVEL_STONE:
                    return "Каменная лопата";
                case SHOVEL_IRON:
                    return "Железная лопата";
                case SHOVEL_DIAMOND:
                    return "Алмазная лопата";
                case BOW:
                    return "Лук";
                case ARROW:
                    return "Стрела";
                case DOOR_CLOSED:
                    return "Дверь (закрыта)";
                case DOOR_OPEN:
                    return "Дверь (открыта)";
                case BG_STONE:
                    return "Каменная стена";
                case BG_DIRT:
                    return "Земляная стена";
                case BG_WOOD:
                    return "Деревянная стена";
                case BG_PLANK:
                    return "Дощатая стена";
                case CRAFT_TABLE:
                    return "Верстак";
                case BOOKSHELF:
                    return "Книжная полка";
                case GLASS:
                    return "Стекло";
                case LANTERN:
                    return "Фонарь";
                case LADDER:
                    return "Лестница";
                case BED:
                    return "Кровать";
                case SIGN:
                    return "Табличка";
                case HELMET_IRON:
                    return "Железный шлем";
                case CHESTPLATE_IRON:
                    return "Железный нагрудник";
                case LEGGINGS_IRON:
                    return "Железные штаны";
                case BOOTS_IRON:
                    return "Железные ботинки";
                case HELMET_DIAMOND:
                    return "Алмазный шлем";
                case CHESTPLATE_DIAMOND:
                    return "Алмазный нагрудник";
                case LEGGINGS_DIAMOND:
                    return "Алмазные штаны";
                case BOOTS_DIAMOND:
                    return "Алмазные ботинки";
                case HELMET_GOLD:
                    return "Золотой шлем";
                case CHESTPLATE_GOLD:
                    return "Золотой нагрудник";
                case LEGGINGS_GOLD:
                    return "Золотые штаны";
                case BOOTS_GOLD:
                    return "Золотые ботинки";
                case HELMET_LEATHER:
                    return "Кожаный шлем";
                case CHESTPLATE_LEATHER:
                    return "Кожаная куртка";
                case LEGGINGS_LEATHER:
                    return "Кожаные штаны";
                case BOOTS_LEATHER:
                    return "Кожаные ботинки";
                case COMMAND_BLOCK:
                    return "Командный блок";
                case APPLE:
                    return "Яблоко";
                case BREAD:
                    return "Хлеб";
                case MEAT:
                    return "Мясо";
                case SLIME_BALL:
                    return "Слизь";
                case STICK:
                    return "Палка";
                default:
                    return "Воздух";
            }
        }
    }

    // ==================== WORKBLOCK ====================
    static class WorkBlock implements Serializable {

        private static final long serialVersionUID = 10L;
        public static final int COOK_TIME = 180;
        int x, y, type;
        ItemStack[] slots;
        int cookTime = 0;
        int currentRecipe = -1;

        WorkBlock(int x, int y, int type, int size) {
            this.x = x;
            this.y = y;
            this.type = type;
            this.slots = new ItemStack[size];
        }

        int getResultCount() {
            return slots.length > 8 && slots[8] != null ? slots[8].count : 0;
        }

        void tickFurnace() {
            if (type != World.FURNACE || slots.length < 9) {
                return;
            }
            ItemStack ore = slots[0];
            ItemStack fuel = slots[1] != null ? slots[1] : slots[2];
            ItemStack result = slots[8];
            int recipe = (ore != null) ? getRecipe(ore.id) : -1;

            if (cookTime > 0 && (recipe == -1 || recipe != currentRecipe)) {
                cookTime = 0;
                currentRecipe = -1;
            }
            if (cookTime > 0) {
                cookTime--;
                if (cookTime <= 0) {
                    if (ore != null && recipe != -1) {
                        if (result == null) {
                            slots[8] = ItemStack.of(recipe, 1);
                        } else if (result.id == recipe && result.count < 999) {
                            result.count++;
                        }
                        ore.count--;
                        if (ore.count <= 0) {
                            slots[0] = null;
                        }
                    }
                    cookTime = 0;
                    currentRecipe = -1;
                }
                return;
            }
            if (ore == null || recipe == -1) {
                return;
            }
            if (result != null && (result.id != recipe || result.count >= 999)) {
                return;
            }
            if (fuel == null || !isFuel(fuel.id)) {
                return;
            }
            fuel.count--;
            if (fuel.count <= 0) {
                if (slots[1] == fuel) {
                    slots[1] = null;
                } else {
                    slots[2] = null;
                }
            }
            cookTime = COOK_TIME;
            currentRecipe = recipe;
        }

        static int getRecipe(int oreId) {
            switch (oreId) {
                case World.IRON:
                    return World.IRON_INGOT;
                case World.GOLD:
                    return World.GOLD_INGOT;
                case World.DIAMOND:
                    return World.DIAMOND_GEM;
                case World.COAL:
                    return World.COAL_ITEM;
                case World.SAND:
                    return World.GLASS;
                default:
                    return -1;
            }
        }

        static boolean isFuel(int id) {
            return id == World.COAL || id == World.COAL_ITEM
                    || id == World.WOOD || id == World.LEAVES || id == World.PLANK;
        }
    }

    // ==================== CHEST LOOT ====================
    static class ChestLoot implements Serializable {

        private static final long serialVersionUID = 1L;
        int x, y;
        ItemStack[] slots;
        boolean generated = false;

        ChestLoot(int x, int y) {
            this.x = x;
            this.y = y;
        }
    }

    // ==================== COMMAND BLOCK DATA ====================
    static class CommandBlockData implements Serializable {

        private static final long serialVersionUID = 1L;
        int x, y;
        String command = "";
        int tickDelay = 0;
        long lastRun = 0;

        CommandBlockData(int x, int y) {
            this.x = x;
            this.y = y;
        }
    }

    // ==================== PLAYER ====================
    static class Player {

        public static final int W = 24;
        public static final int H = 34;

        public double x, y, vx, vy;
        public double cameraX, cameraY;
        public double hp = 100, maxHp = 100;
        public double hunger = 100, maxHunger = 100;
        public int hungerTimer = 0;
        public int hurtCooldown = 0;
        public int animTick = 0;
        public int facing = 1;
        public boolean onGround = false;
        public boolean wasInAir = false;
        public double fallStartY = 0;
        public boolean godMode = false;
        public boolean flyMode = false;
        public ItemStack[] armorSlots = new ItemStack[ARMOR_SLOTS];

        private static final double GRAVITY = 0.7;
        private static final double MOVE_SPEED = 4.5;
        private static final double JUMP_POWER = -12.0;
        private static final double MAX_FALL = 18.0;
        private static final double FRICTION = 0.78;

        public Player(double x, double y) {
            this.x = x;
            this.y = y;
        }

        public int getArmorPoints() {
            if (armorSlots == null) {
                return 0;
            }
            int total = 0;
            for (ItemStack s : armorSlots) {
                if (s != null) {
                    total += Armor.getArmorPoints(s.id);
                }
            }
            return total;
        }

        public void update(double inputX, boolean jump, World world) {
            if (inputX > 0) {
                facing = 1;
            } else if (inputX < 0) {
                facing = -1;
            }

            if (inputX != 0) {
                vx += inputX * 1.3;
            }
            vx *= FRICTION;
            if (Math.abs(vx) > MOVE_SPEED) {
                vx = Math.signum(vx) * MOVE_SPEED;
            }

            if (flyMode) {
                vy = 0;
                if (jump) {
                    vy = -6;
                }
            } else {
                if (jump && onGround) {
                    vy = JUMP_POWER;
                    onGround = false;
                }
                vy += GRAVITY;
                if (vy > MAX_FALL) {
                    vy = MAX_FALL;
                }
            }

            moveX(vx, world);
            moveY(vy, world);

            double targetCamX = x + W / 2.0 - SCREEN_W / 2.0;
            double targetCamY = y + H / 2.0 - SCREEN_H / 2.0;
            cameraX += (targetCamX - cameraX) * 0.15;
            cameraY += (targetCamY - cameraY) * 0.15;
            cameraX = clamp(cameraX, 0, world.getWidth() * TILE - SCREEN_W);
            cameraY = clamp(cameraY, 0, world.getHeight() * TILE - SCREEN_H);

            if (hurtCooldown > 0) {
                hurtCooldown--;
            }
            if (onGround && Math.abs(vx) > 0.5) {
                animTick++;
            }

            if (Modules.HUNGER_SYSTEM) {
                hungerTimer++;
                if (hungerTimer >= 60 * 20) {
                    hungerTimer = 0;
                    hunger -= 1;
                    if (hunger < 0) {
                        hunger = 0;
                    }
                    if (hunger <= 0 && hurtCooldown == 0) {
                        hp -= 1;
                        hurtCooldown = 60;
                    }
                }
            }
        }

        private void moveX(double dx, World world) {
            x += dx;
            int top = (int) (y / TILE);
            int bottom = (int) ((y + H - 1) / TILE);
            if (dx > 0) {
                int right = (int) ((x + W - 1) / TILE);
                for (int ty = top; ty <= bottom; ty++) {
                    if (world.isSolid(right, ty)) {
                        x = right * TILE - W;
                        vx = 0;
                        break;
                    }
                }
            } else if (dx < 0) {
                int left = (int) (x / TILE);
                for (int ty = top; ty <= bottom; ty++) {
                    if (world.isSolid(left, ty)) {
                        x = (left + 1) * TILE;
                        vx = 0;
                        break;
                    }
                }
            }
        }

        private void moveY(double dy, World world) {
            y += dy;
            int left = (int) (x / TILE);
            int right = (int) ((x + W - 1) / TILE);
            if (dy > 0) {
                int bottom = (int) ((y + H - 1) / TILE);
                for (int tx = left; tx <= right; tx++) {
                    if (world.isSolid(tx, bottom)) {
                        y = bottom * TILE - H;
                        vy = 0;
                        onGround = true;
                        break;
                    }
                }
            } else if (dy < 0) {
                int top = (int) (y / TILE);
                for (int tx = left; tx <= right; tx++) {
                    if (world.isSolid(tx, top)) {
                        y = (top + 1) * TILE;
                        vy = 0;
                        break;
                    }
                }
            }
            if (dy >= 0) {
                int bottom = (int) ((y + H) / TILE);
                boolean grounded = false;
                for (int tx = left; tx <= right; tx++) {
                    if (world.isSolid(tx, bottom)) {
                        grounded = true;
                        break;
                    }
                }
                onGround = grounded;
            }
            int maxY = world.getHeight() * TILE - H;
            if (y > maxY) {
                y = maxY;
                vy = 0;
                onGround = true;
            }
            if (y < 0) {
                y = 0;
                vy = 0;
            }
        }

        public void hurt(double dmg) {
            if (godMode) {
                return;
            }
            if (hurtCooldown > 0) {
                return;
            }
            int armorPoints = getArmorPoints();
            double reduction = armorPoints * 0.04;
            if (reduction > 0.8) {
                reduction = 0.8;
            }
            dmg = dmg * (1 - reduction);
            hp -= dmg;
            hurtCooldown = 30;
            Sound.play(Sound.HURT);
        }

        public void draw(Graphics2D g, int camX, int camY) {
            int px = (int) (x - camX);
            int py = (int) (y - camY);
            if (hurtCooldown > 0 && (hurtCooldown / 4) % 2 == 0) {
                return;
            }

            g.setColor(new Color(0, 0, 0, 80));
            g.fillRect(px + 2, py + H - 3, W - 4, 3);

            int legPhase = (animTick / 5) % 4;
            int legOff = legPhase == 0 ? 0 : (legPhase == 1 ? 3 : (legPhase == 2 ? 0 : -3));
            g.setColor(new Color(60, 40, 30));
            g.fillRect(px + 5, py + H - 10 + Math.abs(legOff) / 2, 5, 10 - Math.abs(legOff));
            g.fillRect(px + W - 10, py + H - 10 + Math.abs(-legOff) / 2, 5, 10 - Math.abs(-legOff));

            Color bodyColor = new Color(80, 110, 200);
            if (armorSlots != null && armorSlots[1] != null) {
                int armorId = armorSlots[1].id;
                if (armorId >= World.CHESTPLATE_IRON && armorId <= World.CHESTPLATE_DIAMOND) {
                    bodyColor = new Color(180, 180, 200);
                } else if (armorId >= World.CHESTPLATE_GOLD) {
                    bodyColor = new Color(220, 200, 80);
                } else {
                    bodyColor = new Color(150, 100, 60);
                }
            }
            g.setColor(bodyColor);
            g.fillRect(px + 3, py + 14, W - 6, H - 22);
            g.setColor(new Color(50, 30, 20));
            g.fillRect(px + 3, py + H - 14, W - 6, 3);

            g.setColor(new Color(240, 200, 150));
            int armOff = (animTick / 5) % 4;
            int armY = py + 16 + (armOff == 1 || armOff == 3 ? 1 : 0);
            g.fillRect(px - 1, armY, 4, 12);
            g.fillRect(px + W - 3, armY, 4, 12);

            g.setColor(new Color(250, 210, 160));
            g.fillRect(px + 3, py, W - 6, 14);
            g.setColor(new Color(80, 50, 30));
            g.fillRect(px + 3, py, W - 6, 4);
            g.fillRect(px + 3, py, 3, 8);
            g.fillRect(px + W - 6, py, 3, 8);

            if (armorSlots != null && armorSlots[0] != null) {
                Color helmetColor = new Color(200, 200, 220);
                int hId = armorSlots[0].id;
                if (hId >= World.HELMET_GOLD && hId <= World.HELMET_GOLD + 3) {
                    helmetColor = new Color(220, 200, 80);
                } else if (hId >= World.HELMET_LEATHER) {
                    helmetColor = new Color(150, 100, 60);
                }
                g.setColor(helmetColor);
                g.fillRect(px + 1, py - 2, W - 2, 12);
                g.setColor(new Color(0, 0, 0, 100));
                g.fillRect(px + 3, py + 6, W - 6, 5);
            }

            g.setColor(Color.WHITE);
            int eyeY = py + 6;
            if (facing == 1) {
                g.fillRect(px + 9, eyeY, 4, 4);
                g.fillRect(px + 15, eyeY, 4, 4);
                g.setColor(new Color(30, 60, 130));
                g.fillRect(px + 11, eyeY + 1, 2, 3);
                g.fillRect(px + 17, eyeY + 1, 2, 3);
            } else {
                g.fillRect(px + 5, eyeY, 4, 4);
                g.fillRect(px + 11, eyeY, 4, 4);
                g.setColor(new Color(30, 60, 130));
                g.fillRect(px + 5, eyeY + 1, 2, 3);
                g.fillRect(px + 11, eyeY + 1, 2, 3);
            }
        }

        private static double clamp(double v, double min, double max) {
            return Math.max(min, Math.min(max, v));
        }
    }

    // ==================== MONSTER ====================
    static class Monster {

        public static final int W = 24;
        public static final int H = 30;
        double x, y, vx, vy;
        int type;
        double hp, maxHp;
        boolean dead = false;
        boolean onGround = false;
        int direction = 1;
        int jumpCooldown = 0;
        int attackCooldown = 0;
        int animTick = 0;
        private static final double GRAVITY = 0.6;

        Monster(double x, double y, int type) {
            this.x = x;
            this.y = y;
            this.type = type;
            switch (type) {
                case 0:
                    hp = maxHp = 30;
                    break;
                case 1:
                    hp = maxHp = 40;
                    break;
                case 2:
                    hp = maxHp = 20;
                    break;
                case 3:
                    hp = maxHp = 35;
                    break;
                case 4:
                    hp = maxHp = 25;
                    break;
                default:
                    hp = maxHp = 30;
            }
        }

        ItemStack getLoot(Random rnd) {
            switch (type) {
                case 0:
                    return ItemStack.of(World.DIRT, 1 + rnd.nextInt(2));
                case 1:
                    return ItemStack.of(World.ARROW, 1 + rnd.nextInt(3));
                case 2:
                    return ItemStack.of(World.SLIME_BALL, 1);
                case 3:
                    return ItemStack.of(World.COAL_ITEM, 1);
                case 4:
                    return ItemStack.of(World.WOOD, 1);
                default:
                    return ItemStack.of(World.STONE, 1);
            }
        }

        void update(Player player, World world, List<Monster> others) {
            if (dead) {
                return;
            }
            animTick++;
            double dx = player.x - x;
            double dy = player.y - y;
            direction = dx > 0 ? 1 : -1;

            vx += direction * 0.3;
            vx *= 0.85;
            if (Math.abs(vx) > 2.2) {
                vx = Math.signum(vx) * 2.2;
            }

            if (onGround && jumpCooldown <= 0) {
                int aheadX = (int) ((x + (direction > 0 ? W + 2 : -2)) / TILE);
                int belowY = (int) ((y + H + 2) / TILE);
                int aheadY = (int) ((y + H - 4) / TILE);
                if (world.isSolid(aheadX, aheadY) || !world.isSolid(aheadX, belowY)) {
                    vy = -8;
                    onGround = false;
                }
                jumpCooldown = 30;
            }
            if (jumpCooldown > 0) {
                jumpCooldown--;
            }
            vy += GRAVITY;
            if (vy > 15) {
                vy = 15;
            }
            moveX(vx, world);
            moveY(vy, world);

            if (attackCooldown > 0) {
                attackCooldown--;
            }
            if (attackCooldown == 0) {
                Rectangle mr = new Rectangle((int) x, (int) y, W, H);
                Rectangle pr = new Rectangle((int) player.x, (int) player.y, Player.W, Player.H);
                if (mr.intersects(pr)) {
                    int dmg = 8;
                    if (type == 1) {
                        dmg = 10;
                    }
                    if (type == 3) {
                        dmg = 20;
                    }
                    if (type == 4) {
                        dmg = 6;
                    }
                    player.hurt(dmg);
                    attackCooldown = 40;
                    if (type == 3) {
                        dead = true;
                    }
                }
            }
        }

        void moveX(double dx, World world) {
            x += dx;
            int top = (int) (y / TILE);
            int bottom = (int) ((y + H - 1) / TILE);
            if (dx > 0) {
                int right = (int) ((x + W - 1) / TILE);
                for (int ty = top; ty <= bottom; ty++) {
                    if (world.isSolid(right, ty)) {
                        x = right * TILE - W;
                        vx = 0;
                        break;
                    }
                }
            } else if (dx < 0) {
                int left = (int) (x / TILE);
                for (int ty = top; ty <= bottom; ty++) {
                    if (world.isSolid(left, ty)) {
                        x = (left + 1) * TILE;
                        vx = 0;
                        break;
                    }
                }
            }
        }

        void moveY(double dy, World world) {
            y += dy;
            int left = (int) (x / TILE);
            int right = (int) ((x + W - 1) / TILE);
            if (dy > 0) {
                int bottom = (int) ((y + H - 1) / TILE);
                for (int tx = left; tx <= right; tx++) {
                    if (world.isSolid(tx, bottom)) {
                        y = bottom * TILE - H;
                        vy = 0;
                        onGround = true;
                        break;
                    }
                }
            } else if (dy < 0) {
                int top = (int) (y / TILE);
                for (int tx = left; tx <= right; tx++) {
                    if (world.isSolid(tx, top)) {
                        y = (top + 1) * TILE;
                        vy = 0;
                        break;
                    }
                }
            }
            if (dy >= 0) {
                int bottom = (int) ((y + H) / TILE);
                boolean grounded = false;
                for (int tx = left; tx <= right; tx++) {
                    if (world.isSolid(tx, bottom)) {
                        grounded = true;
                        break;
                    }
                }
                onGround = grounded;
            }
        }

        void draw(Graphics2D g, int camX, int camY) {
            int px = (int) (x - camX);
            int py = (int) (y - camY);
            g.setColor(new Color(0, 0, 0, 60));
            g.fillOval(px + 2, py + H - 2, W - 4, 6);

            switch (type) {
                case 0:
                    g.setColor(new Color(80, 140, 80));
                    g.fillRect(px + 3, py, W - 6, H - 4);
                    g.setColor(new Color(60, 100, 60));
                    g.fillRect(px + 2, py + 8, 3, 12);
                    g.fillRect(px + W - 5, py + 8, 3, 12);
                    g.setColor(new Color(40, 20, 20));
                    g.fillRect(px + 6, py + 6, 4, 4);
                    g.fillRect(px + W - 10, py + 6, 4, 4);
                    break;
                case 1:
                    g.setColor(new Color(230, 230, 220));
                    g.fillRect(px + 4, py + 4, W - 8, H - 6);
                    g.setColor(new Color(200, 200, 190));
                    g.fillRect(px + W / 2 - 1, py + 10, 2, H - 14);
                    g.fillRect(px + 4, py + 14, W - 8, 2);
                    g.fillRect(px + 4, py + 20, W - 8, 2);
                    g.setColor(new Color(60, 60, 60));
                    g.fillRect(px + 6, py + 6, 4, 5);
                    g.fillRect(px + W - 10, py + 6, 4, 5);
                    break;
                case 2:
                    g.setColor(new Color(120, 200, 120, 220));
                    int squash = (int) (Math.sin(animTick * 0.15) * 3);
                    g.fillOval(px, py + squash, W, H - squash);
                    g.setColor(new Color(80, 160, 80));
                    g.fillOval(px + 5, py + 6 + squash, W - 10, H - 14);
                    g.setColor(Color.BLACK);
                    g.fillRect(px + 7, py + 10, 3, 3);
                    g.fillRect(px + W - 10, py + 10, 3, 3);
                    break;
                case 3:
                    g.setColor(new Color(60, 180, 60));
                    g.fillRect(px + 3, py, W - 6, H);
                    g.setColor(new Color(0, 0, 0, 120));
                    g.fillRect(px + 6, py + 8, 4, 4);
                    g.fillRect(px + W - 10, py + 8, 4, 4);
                    g.fillRect(px + 8, py + 16, 8, 6);
                    break;
                case 4:
                    g.setColor(new Color(50, 50, 60));
                    g.fillOval(px + 2, py + 6, W - 4, H - 12);
                    g.setColor(new Color(30, 30, 40));
                    for (int i = 0; i < 4; i++) {
                        g.fillRect(px - 4 + i * 8, py + 10, 2, 8);
                        g.fillRect(px - 4 + i * 8, py + 18, 2, 8);
                    }
                    g.setColor(Color.RED);
                    g.fillRect(px + 7, py + 10, 3, 3);
                    g.fillRect(px + W - 10, py + 10, 3, 3);
                    break;
            }

            if (hp < maxHp) {
                g.setColor(Color.BLACK);
                g.fillRect(px, py - 8, W, 4);
                g.setColor(Color.RED);
                g.fillRect(px, py - 8, (int) (W * (hp / maxHp)), 4);
            }
        }
    }

    // ==================== ANIMAL ====================
    static class Animal {

        public static final int W = 24;
        public static final int H = 24;
        double x, y, vx, vy;
        int type;
        double hp, maxHp;
        boolean dead = false;
        boolean onGround = false;
        int direction = 1;
        int animTick = 0;
        int hurtTimer = 0;
        int wanderTimer = 0;
        private static final double GRAVITY = 0.6;

        Animal(double x, double y, int type) {
            this.x = x;
            this.y = y;
            this.type = type;
            switch (type) {
                case 0:
                    hp = maxHp = 10;
                    break;
                case 1:
                    hp = maxHp = 10;
                    break;
                case 2:
                    hp = maxHp = 8;
                    break;
                case 3:
                    hp = maxHp = 4;
                    break;
            }
        }

        ItemStack getDrop(Random rnd) {
            switch (type) {
                case 0:
                    return ItemStack.of(World.MEAT, 1 + rnd.nextInt(3));
                case 1:
                    return ItemStack.of(World.MEAT, 1 + rnd.nextInt(3));
                case 2:
                    return ItemStack.of(World.LEAVES, 1);
                case 3:
                    return ItemStack.of(World.MEAT, 1);
                default:
                    return null;
            }
        }

        void update(World world, Player player) {
            if (dead) {
                return;
            }
            animTick++;
            if (hurtTimer > 0) {
                hurtTimer--;
            }

            double dx = x - player.x;
            double dist = Math.abs(dx);

            wanderTimer++;
            if (wanderTimer > 100) {
                wanderTimer = 0;
                if (dist < 100) {
                    vx += Math.signum(dx) * 0.5;
                } else if (Math.random() < 0.3) {
                    vx += (Math.random() - 0.5) * 1.0;
                }
            }
            vx *= 0.9;
            if (Math.abs(vx) > 2) {
                vx = Math.signum(vx) * 2;
            }
            if (Math.abs(vx) > 0.2) {
                direction = vx > 0 ? 1 : -1;
            }

            vy += GRAVITY;
            if (vy > 15) {
                vy = 15;
            }

            moveX(vx, world);
            moveY(vy, world);
        }

        void moveX(double dx, World world) {
            x += dx;
            int top = (int) (y / TILE);
            int bottom = (int) ((y + H - 1) / TILE);
            if (dx > 0) {
                int right = (int) ((x + W - 1) / TILE);
                for (int ty = top; ty <= bottom; ty++) {
                    if (world.isSolid(right, ty)) {
                        x = right * TILE - W;
                        vx = 0;
                        break;
                    }
                }
            } else if (dx < 0) {
                int left = (int) (x / TILE);
                for (int ty = top; ty <= bottom; ty++) {
                    if (world.isSolid(left, ty)) {
                        x = (left + 1) * TILE;
                        vx = 0;
                        break;
                    }
                }
            }
        }

        void moveY(double dy, World world) {
            y += dy;
            int left = (int) (x / TILE);
            int right = (int) ((x + W - 1) / TILE);
            if (dy > 0) {
                int bottom = (int) ((y + H - 1) / TILE);
                for (int tx = left; tx <= right; tx++) {
                    if (world.isSolid(tx, bottom)) {
                        y = bottom * TILE - H;
                        vy = 0;
                        onGround = true;
                        break;
                    }
                }
            } else if (dy < 0) {
                int top = (int) (y / TILE);
                for (int tx = left; tx <= right; tx++) {
                    if (world.isSolid(tx, top)) {
                        y = (top + 1) * TILE;
                        vy = 0;
                        break;
                    }
                }
            }
            if (dy >= 0) {
                int bottom = (int) ((y + H) / TILE);
                boolean grounded = false;
                for (int tx = left; tx <= right; tx++) {
                    if (world.isSolid(tx, bottom)) {
                        grounded = true;
                        break;
                    }
                }
                onGround = grounded;
            }
        }

        void draw(Graphics2D g, int camX, int camY) {
            int px = (int) (x - camX);
            int py = (int) (y - camY);
            g.setColor(new Color(0, 0, 0, 60));
            g.fillOval(px + 2, py + H - 2, W - 4, 6);

            if (hurtTimer > 0 && (hurtTimer / 3) % 2 == 0) {
                return;
            }

            switch (type) {
                case 0:
                    g.setColor(new Color(240, 180, 180));
                    g.fillRect(px + 2, py + 6, W - 4, H - 8);
                    g.setColor(new Color(200, 140, 140));
                    g.fillRect(px + 4, py + 2, 6, 6);
                    g.setColor(Color.BLACK);
                    g.fillRect(px + 5, py + 4, 2, 2);
                    g.fillRect(px + 9, py + 4, 2, 2);
                    break;
                case 1:
                    g.setColor(new Color(80, 60, 40));
                    g.fillRect(px + 2, py + 6, W - 4, H - 8);
                    g.setColor(new Color(240, 240, 240));
                    g.fillRect(px + 6, py + 8, 4, 4);
                    g.fillRect(px + 14, py + 12, 3, 3);
                    g.setColor(new Color(60, 40, 30));
                    g.fillRect(px + 4, py + 2, 6, 6);
                    break;
                case 2:
                    g.setColor(new Color(240, 240, 240));
                    g.fillOval(px + 2, py + 4, W - 4, H - 8);
                    g.setColor(new Color(60, 50, 40));
                    g.fillRect(px + 6, py + 2, 6, 4);
                    break;
                case 3:
                    g.setColor(new Color(240, 240, 240));
                    g.fillOval(px + 4, py + 8, W - 8, H - 12);
                    g.fillRect(px + 6, py + 4, 6, 5);
                    g.setColor(new Color(240, 200, 50));
                    g.fillRect(px + 11, py + 5, 4, 2);
                    g.setColor(Color.BLACK);
                    g.fillRect(px + 7, py + 5, 1, 1);
                    g.setColor(new Color(200, 50, 50));
                    g.fillRect(px + 6, py + 1, 3, 2);
                    break;
            }
        }
    }

    // ==================== VILLAGER ====================
    static class Villager {

        double x, y, vx, vy;
        int type;
        int level = 1;
        int xp = 0;
        int direction = 1;
        int animTick = 0;
        boolean onGround = false;
        double homeX;
        private static final double GRAVITY = 0.6;

        Villager(double x, double y, int type) {
            this.x = x;
            this.y = y;
            this.type = type;
            this.homeX = x;
        }

        List<TradeRecipe> getRecipes() {
            List<TradeRecipe> list = new ArrayList<>();
            list.add(new TradeRecipe(World.DIRT, 20, 1));
            list.add(new TradeRecipe(World.STONE, 20, 1));
            list.add(new TradeRecipe(World.WOOD, 10, 2));
            list.add(new TradeRecipe(World.PLANK, 15, 3));
            list.add(new TradeRecipe(World.STICK, 20, 2));
            list.add(new TradeRecipe(World.TORCH, 5, 2));
            list.add(new TradeRecipe(World.COAL, 10, 3));
            list.add(new TradeRecipe(World.IRON, 3, 8));
            list.add(new TradeRecipe(World.IRON_INGOT, 1, 15));
            list.add(new TradeRecipe(World.GOLD, 1, 25));
            list.add(new TradeRecipe(World.GOLD_INGOT, 1, 40));
            if (level >= 2) {
                list.add(new TradeRecipe(World.DIAMOND, 1, 80));
                list.add(new TradeRecipe(World.DIAMOND_GEM, 1, 150));
                list.add(new TradeRecipe(World.APPLE, 5, 10));
            }
            if (level >= 3) {
                list.add(new TradeRecipe(World.FURNACE, 1, 100));
                list.add(new TradeRecipe(World.CHEST, 1, 80));
                list.add(new TradeRecipe(World.WORKBENCH, 1, 50));
                list.add(new TradeRecipe(World.HELMET_IRON, 1, 200));
            }
            return list;
        }

        void update(World world) {
            animTick++;
            vx *= 0.9;
            if (Math.abs(vx) < 0.3 && animTick % 60 == 0) {
                vx = (new Random().nextBoolean() ? 1 : -1) * 0.8;
            }
            if (Math.abs(x - homeX) > TILE * 5) {
                vx = Math.signum(homeX - x) * 0.8;
            }
            vy += GRAVITY;
            if (vy > 15) {
                vy = 15;
            }
            moveX(vx, world);
            moveY(vy, world);
        }

        void moveX(double dx, World world) {
            x += dx;
            int top = (int) (y / TILE);
            int bottom = (int) ((y + Player.H - 1) / TILE);
            if (dx > 0) {
                int right = (int) ((x + Player.W - 1) / TILE);
                for (int ty = top; ty <= bottom; ty++) {
                    if (world.isSolid(right, ty)) {
                        x = right * TILE - Player.W;
                        vx = 0;
                        break;
                    }
                }
            } else if (dx < 0) {
                int left = (int) (x / TILE);
                for (int ty = top; ty <= bottom; ty++) {
                    if (world.isSolid(left, ty)) {
                        x = (left + 1) * TILE;
                        vx = 0;
                        break;
                    }
                }
            }
        }

        void moveY(double dy, World world) {
            y += dy;
            int left = (int) (x / TILE);
            int right = (int) ((x + Player.W - 1) / TILE);
            if (dy > 0) {
                int bottom = (int) ((y + Player.H - 1) / TILE);
                for (int tx = left; tx <= right; tx++) {
                    if (world.isSolid(tx, bottom)) {
                        y = bottom * TILE - Player.H;
                        vy = 0;
                        onGround = true;
                        break;
                    }
                }
            } else if (dy < 0) {
                int top = (int) (y / TILE);
                for (int tx = left; tx <= right; tx++) {
                    if (world.isSolid(tx, top)) {
                        y = (top + 1) * TILE;
                        vy = 0;
                        break;
                    }
                }
            }
        }

        void draw(Graphics2D g, int camX, int camY) {
            int px = (int) (x - camX);
            int py = (int) (y - camY);
            g.setColor(new Color(0, 0, 0, 60));
            g.fillOval(px + 2, py + Player.H - 2, Player.W - 4, 6);
            Color body = type == 0 ? new Color(180, 120, 80)
                    : type == 1 ? new Color(120, 160, 200)
                            : new Color(160, 100, 160);
            g.setColor(body);
            g.fillRect(px + 3, py + 14, Player.W - 6, Player.H - 22);
            g.setColor(new Color(240, 200, 160));
            g.fillRect(px + 3, py, Player.W - 6, 14);
            g.setColor(new Color(230, 180, 140));
            if (direction > 0) {
                g.fillRect(px + Player.W - 3, py + 6, 5, 4);
            } else {
                g.fillRect(px - 2, py + 6, 5, 4);
            }
            g.setColor(new Color(80, 40, 20));
            g.fillRect(px + 7, py + 5, 3, 3);
            g.fillRect(px + Player.W - 10, py + 5, 3, 3);
            g.setColor(new Color(60, 40, 30));
            g.fillRect(px + 5, py + Player.H - 10, 5, 10);
            g.fillRect(px + Player.W - 10, py + Player.H - 10, 5, 10);
            g.setColor(new Color(255, 220, 100));
            g.setFont(PixelFont.font(14, Font.BOLD));
            g.drawString("$", px + Player.W / 2 - 4, py - 4);
        }
    }

    // ==================== TRADE RECIPE ====================
    static class TradeRecipe {

        int itemId, count, priceGold;

        TradeRecipe(int itemId, int count, int priceGold) {
            this.itemId = itemId;
            this.count = count;
            this.priceGold = priceGold;
        }
    }

    // ==================== ARROW ====================
    static class Arrow {

        double x, y, vx, vy;
        boolean dead = false;
        int life = 200;
        private static final double GRAVITY = 0.3;

        Arrow(double x, double y, double vx, double vy) {
            this.x = x;
            this.y = y;
            this.vx = vx;
            this.vy = vy;
        }

        void update(World world, List<Monster> monsters) {
            x += vx;
            y += vy;
            vy += GRAVITY;
            life--;
            if (life <= 0) {
                dead = true;
                return;
            }
            int tx = (int) (x / TILE);
            int ty = (int) (y / TILE);
            if (world.isSolid(tx, ty)) {
                dead = true;
                return;
            }
            for (Monster m : monsters) {
                if (x >= m.x - 4 && x <= m.x + Monster.W + 4
                        && y >= m.y - 4 && y <= m.y + Monster.H + 4) {
                    m.hp -= 8;
                    dead = true;
                    return;
                }
            }
        }

        void draw(Graphics2D g, int camX, int camY) {
            int px = (int) (x - camX);
            int py = (int) (y - camY);
            g.setColor(new Color(100, 80, 60));
            g.fillRect(px - 4, py - 1, 8, 2);
            g.setColor(new Color(200, 200, 200));
            g.fillRect(px + 3, py - 2, 4, 4);
        }
    }

    // ==================== REMOTE PLAYER ====================
    static class RemotePlayer {

        int id;
        double x, y;
        int facing = 1;
        String name = "Игрок";
        long lastUpdate = System.currentTimeMillis();
        double targetX, targetY;

        RemotePlayer(int id, double x, double y) {
            this.id = id;
            this.x = x;
            this.y = y;
            this.targetX = x;
            this.targetY = y;
            this.name = "Игрок #" + id;
        }

        void updatePosition(double nx, double ny, int facing) {
            this.targetX = nx;
            this.targetY = ny;
            this.facing = facing;
            this.lastUpdate = System.currentTimeMillis();
        }

        void tick() {
            x += (targetX - x) * 0.25;
            y += (targetY - y) * 0.25;
        }

        void draw(Graphics2D g, int camX, int camY) {
            int px = (int) (x - camX);
            int py = (int) (y - camY);
            g.setColor(new Color(0, 0, 0, 80));
            g.fillRect(px + 2, py + Player.H - 3, Player.W - 4, 3);
            g.setColor(new Color(180, 80, 200));
            g.fillRect(px + 3, py + 14, Player.W - 6, Player.H - 22);
            g.setColor(new Color(50, 30, 20));
            g.fillRect(px + 3, py + Player.H - 14, Player.W - 6, 3);
            g.setColor(new Color(240, 200, 150));
            g.fillRect(px - 1, py + 16, 4, 12);
            g.fillRect(px + Player.W - 3, py + 16, 4, 12);
            g.setColor(new Color(250, 210, 160));
            g.fillRect(px + 3, py, Player.W - 6, 14);
            g.setColor(new Color(180, 80, 30));
            g.fillRect(px + 3, py, Player.W - 6, 4);
            g.setColor(Color.WHITE);
            int eyeY = py + 6;
            if (facing == 1) {
                g.fillRect(px + 9, eyeY, 4, 4);
                g.fillRect(px + 15, eyeY, 4, 4);
            } else {
                g.fillRect(px + 5, eyeY, 4, 4);
                g.fillRect(px + 11, eyeY, 4, 4);
            }
            g.setFont(PixelFont.font(11, Font.BOLD));
            g.setColor(new Color(0, 0, 0, 180));
            FontMetrics fm = g.getFontMetrics();
            int tw = fm.stringWidth(name);
            g.fillRect(px + Player.W / 2 - tw / 2 - 3, py - 18, tw + 6, 14);
            g.setColor(new Color(255, 200, 255));
            g.drawString(name, px + Player.W / 2 - tw / 2, py - 8);
        }
    }

    // ==================== DUNGEON ====================
    static class Dungeon implements Serializable {

        private static final long serialVersionUID = 2L;
        int centerX, centerY;
        int rooms;
        List<int[]> roomPositions = new ArrayList<>();
        boolean discovered = false;

        Dungeon(int cx, int cy, Random rnd) {
            this.centerX = cx;
            this.centerY = cy;
            this.rooms = 3 + rnd.nextInt(2);
            for (int i = 0; i < rooms; i++) {
                int rx = cx + (i - rooms / 2) * 14 + rnd.nextInt(6) - 3;
                int ry = cy + rnd.nextInt(6) - 3;
                roomPositions.add(new int[]{rx, ry});
            }
        }

        void buildIn(World world) {
            try {
                Random rnd = new Random(centerX * 31L + centerY);
                for (int[] pos : roomPositions) {
                    buildRoom(world, pos[0], pos[1], rnd);
                }
                for (int i = 0; i < roomPositions.size() - 1; i++) {
                    int[] a = roomPositions.get(i);
                    int[] b = roomPositions.get(i + 1);
                    buildCorridor(world, a[0], a[1], b[0], b[1], rnd);
                }
            } catch (Exception ex) {
                System.out.println(">>> Ошибка в Dungeon.buildIn: " + ex.getMessage());
            }
        }

        private void buildRoom(World world, int cx, int cy, Random rnd) {
            int w = 7;
            int h = 5;
            int left = cx - w / 2;
            int right = cx + w / 2;
            int top = cy - h / 2;
            int bottom = cy + h / 2;
            if (left < 2 || right > world.getWidth() - 3) {
                return;
            }
            if (top < 2 || bottom > world.getHeight() - 3) {
                return;
            }

            for (int x = left; x <= right; x++) {
                for (int y = top; y <= bottom; y++) {
                    boolean isWall = (x == left || x == right || y == top || y == bottom);
                    if (isWall) {
                        world.setBlock(x, y, World.STONE);
                        world.setBackground(x, y, World.BG_STONE);
                    } else {
                        world.setBlock(x, y, World.AIR);
                        world.setBackground(x, y, World.BG_STONE);
                    }
                }
            }

            if (world.inBounds(left + 2, top + 1)) {
                world.setBlock(left + 2, top + 1, World.TORCH);
            }
            if (world.inBounds(right - 2, top + 1)) {
                world.setBlock(right - 2, top + 1, World.TORCH);
            }

            int chestX = cx;
            int chestY = cy;
            if (world.inBounds(chestX, chestY) && world.getBlock(chestX, chestY) == World.AIR) {
                world.setBlock(chestX, chestY, World.CHEST);
                ChestLoot loot = new ChestLoot(chestX, chestY);
                loot.slots = new ItemStack[27];
                Random lr = new Random(chestX * 17L + chestY);
                loot.slots[0] = ItemStack.of(World.DIAMOND_GEM, 1 + lr.nextInt(3));
                loot.slots[1] = ItemStack.of(World.GOLD_INGOT, 2 + lr.nextInt(4));
                loot.slots[2] = ItemStack.of(World.IRON_INGOT, 3 + lr.nextInt(5));
                loot.slots[3] = ItemStack.of(World.COIN_GOLD, 20 + lr.nextInt(80));
                loot.slots[4] = ItemStack.of(World.APPLE, 2 + lr.nextInt(4));
                if (lr.nextBoolean()) {
                    loot.slots[5] = ItemStack.of(World.HELMET_IRON, 1);
                }
                if (lr.nextBoolean()) {
                    loot.slots[6] = ItemStack.of(World.SWORD_IRON, 1);
                }
                if (lr.nextInt(4) == 0) {
                    loot.slots[7] = ItemStack.of(World.DIAMOND_GEM, 5);
                }
                loot.generated = true;
                world.chestLoot.add(loot);
            }
        }

        private void buildCorridor(World world, int x1, int y1, int x2, int y2, Random rnd) {
            int minX = Math.min(x1, x2);
            int maxX = Math.max(x1, x2);
            if (maxX - minX > 60) {
                return;
            }
            for (int x = minX; x <= maxX; x++) {
                for (int dy = -1; dy <= 1; dy++) {
                    int ty = y1 + dy;
                    if (world.inBounds(x, ty)) {
                        world.setBlock(x, ty, World.AIR);
                        world.setBackground(x, ty, World.BG_STONE);
                    }
                }
                if (world.inBounds(x, y1 - 2)) {
                    world.setBlock(x, y1 - 2, World.STONE);
                }
                if (world.inBounds(x, y1 + 2)) {
                    world.setBlock(x, y1 + 2, World.STONE);
                }
            }
            int minY = Math.min(y1, y2);
            int maxY = Math.max(y1, y2);
            if (maxY - minY > 60) {
                return;
            }
            for (int y = minY; y <= maxY; y++) {
                for (int dx = -1; dx <= 1; dx++) {
                    int tx = x2 + dx;
                    if (world.inBounds(tx, y)) {
                        world.setBlock(tx, y, World.AIR);
                        world.setBackground(tx, y, World.BG_STONE);
                    }
                }
                if (world.inBounds(x2 - 2, y)) {
                    world.setBlock(x2 - 2, y, World.STONE);
                }
                if (world.inBounds(x2 + 2, y)) {
                    world.setBlock(x2 + 2, y, World.STONE);
                }
            }
        }
    }

    // ==================== ACHIEVEMENT ====================
    static class Achievement {

        String id, title, description, category;
        boolean unlocked = false;

        Achievement(String id, String title, String desc, String cat) {
            this.id = id;
            this.title = title;
            this.description = desc;
            this.category = cat;
        }
    }

    // ==================== FLOATING TEXT ====================
    static class FloatingText {

        String text;
        double x, y;
        Color color;
        int life = 70;

        FloatingText(String t, double x, double y, Color c) {
            this.text = t;
            this.x = x;
            this.y = y;
            this.color = c;
        }
    }

    // ==================== CHAT MESSAGE ====================
    static class ChatMessage {

        String text;
        Color color;
        long time;

        ChatMessage(String t, Color c, long time) {
            this.text = t;
            this.color = c;
            this.time = time;
        }
    }

    // ==================== WORLD SAVE ====================
    static class WorldSave {

        File file;
        String name;
        long size;
        String dateStr;
        int sizeW, sizeH;
        WorldType worldType;
        GameMode mode;
        long iconSeed;
    }

    // ==================== SOUND ====================
    static class Sound {

        public static final int CLICK = 0;
        public static final int MINE = 1;
        public static final int HIT = 2;
        public static final int HURT = 3;
        public static final int TRADE = 4;
        public static final int ACHIEVEMENT = 5;
        public static final int DEATH = 6;
        public static final int START = 7;
        public static final int JUMP = 8;
        public static final int PLACE = 9;
        public static final int OPEN_CHEST = 10;
        public static final int CRAFT = 11;

        private static boolean enabled = true;
        private static float volume = 0.7f;
        private static Map<Integer, String> files = new HashMap<>();
        private static Map<Integer, byte[]> cache = new HashMap<>();

        static {
            files.put(CLICK, "resources/sounds/sfx/click.wav");
            files.put(MINE, "resources/sounds/sfx/dig.wav");
            files.put(HIT, "resources/sounds/sfx/hit.wav");
            files.put(HURT, "resources/sounds/sfx/hurt.wav");
            files.put(TRADE, "resources/sounds/sfx/trade.wav");
            files.put(ACHIEVEMENT, "resources/sounds/sfx/achievement.wav");
            files.put(DEATH, "resources/sounds/sfx/death.wav");
            files.put(START, "resources/sounds/sfx/start.wav");
            files.put(JUMP, "resources/sounds/sfx/jump.wav");
            files.put(PLACE, "resources/sounds/sfx/place.wav");
            files.put(OPEN_CHEST, "resources/sounds/sfx/open_chest.wav");
            files.put(CRAFT, "resources/sounds/sfx/craft.wav");
        }

        static void init() {
            try {
                AudioFormat fmt = new AudioFormat(44100, 16, 1, true, false);
                DataLine.Info info = new DataLine.Info(SourceDataLine.class, fmt);
                if (!AudioSystem.isLineSupported(info)) {
                    enabled = false;
                }
            } catch (Exception e) {
                enabled = false;
            }
        }

        static void setVolume(float v) {
            volume = Math.max(0f, Math.min(1f, v));
        }

        public static void play(final int soundId) {
            if (!enabled) {
                return;
            }
            new Thread(() -> {
                try {
                    String path = files.get(soundId);
                    InputStream is = null;
                    if (path != null) {
                        File f = new File(path);
                        if (f.exists()) {
                            is = new FileInputStream(f);
                        }
                    }
                    if (is == null && path != null) {
                        is = Sound.class.getResourceAsStream("/" + path);
                    }

                    if (is != null) {
                        AudioInputStream ais = AudioSystem.getAudioInputStream(is);
                        Clip clip = AudioSystem.getClip();
                        clip.open(ais);
                        try {
                            FloatControl vol = (FloatControl) clip.getControl(FloatControl.Type.MASTER_GAIN);
                            float dB = (float) (Math.log10(Math.max(0.0001, volume)) * 20.0);
                            vol.setValue(dB);
                        } catch (Exception ignored) {
                        }
                        clip.start();
                        Thread.sleep(clip.getMicrosecondLength() / 1000 + 50);
                        clip.close();
                        return;
                    }

                    byte[] data = cache.get(soundId);
                    if (data == null) {
                        data = generate(soundId);
                        cache.put(soundId, data);
                    }
                    AudioFormat fmt = new AudioFormat(44100, 16, 1, true, false);
                    SourceDataLine line = (SourceDataLine) AudioSystem.getLine(
                            new DataLine.Info(SourceDataLine.class, fmt));
                    line.open(fmt);
                    line.start();
                    line.write(data, 0, data.length);
                    line.drain();
                    line.close();
                } catch (Exception ignored) {
                }
            }).start();
        }

        private static byte[] generate(int soundId) {
            int sampleRate = 44100;
            double duration, freq;
            int waveform;
            switch (soundId) {
                case CLICK:
                    duration = 0.04;
                    freq = 800;
                    waveform = 0;
                    break;
                case MINE:
                    duration = 0.08;
                    freq = 200;
                    waveform = 1;
                    break;
                case HIT:
                    duration = 0.06;
                    freq = 150;
                    waveform = 1;
                    break;
                case HURT:
                    duration = 0.20;
                    freq = 100;
                    waveform = 2;
                    break;
                case TRADE:
                    duration = 0.30;
                    freq = 660;
                    waveform = 0;
                    break;
                case ACHIEVEMENT:
                    duration = 0.50;
                    freq = 880;
                    waveform = 0;
                    break;
                case DEATH:
                    duration = 0.80;
                    freq = 80;
                    waveform = 2;
                    break;
                case START:
                    duration = 0.40;
                    freq = 440;
                    waveform = 0;
                    break;
                case JUMP:
                    duration = 0.10;
                    freq = 500;
                    waveform = 0;
                    break;
                case PLACE:
                    duration = 0.08;
                    freq = 300;
                    waveform = 1;
                    break;
                case OPEN_CHEST:
                    duration = 0.30;
                    freq = 400;
                    waveform = 0;
                    break;
                case CRAFT:
                    duration = 0.25;
                    freq = 600;
                    waveform = 0;
                    break;
                default:
                    duration = 0.1;
                    freq = 440;
                    waveform = 0;
            }
            int n = (int) (sampleRate * duration);
            byte[] buf = new byte[n * 2];
            for (int i = 0; i < n; i++) {
                double t = i / (double) sampleRate;
                double env = Math.exp(-4 * t / duration);
                double v;
                if (waveform == 0) {
                    v = Math.sin(2 * Math.PI * freq * t);
                } else if (waveform == 1) {
                    v = (Math.random() * 2 - 1);
                } else {
                    double f = freq * (1 - t * 1.5);
                    v = Math.signum(Math.sin(2 * Math.PI * f * t));
                }
                short s = (short) (v * env * 8000 * volume);
                buf[i * 2] = (byte) (s & 0xFF);
                buf[i * 2 + 1] = (byte) ((s >> 8) & 0xFF);
            }
            return buf;
        }
    }

    // ==================== MUSIC ====================
    static class Music {

        private static SourceDataLine line;
        private static Thread thread;
        private static volatile boolean playing = false;
        private static volatile boolean running = false;
        private static float volume = 0.55f;
        private static String currentTrack = null;

        public static void playMenuMusic() {
            playFile("resources/sounds/music/menu_music.wav");
        }

        public static void playGameMusic() {
            playFile("resources/sounds/music/game_music.wav");
        }

        public static void playFile(String path) {
            if (playing && path.equals(currentTrack)) {
                return;
            }
            stop();
            currentTrack = path;

            File f = new File(path);
            if (!f.exists()) {
                InputStream test = Music.class.getResourceAsStream("/" + path);
                if (test == null) {
                    playProcedural();
                    return;
                }
                try {
                    test.close();
                } catch (Exception ignored) {
                }
            }

            playing = true;
            running = true;
            final File finalFile = f;
            thread = new Thread(() -> {
                try {
                    while (running) {
                        AudioInputStream ais;
                        if (finalFile.exists()) {
                            ais = AudioSystem.getAudioInputStream(finalFile);
                        } else {
                            InputStream is = Music.class.getResourceAsStream("/" + path);
                            ais = AudioSystem.getAudioInputStream(is);
                        }
                        AudioFormat format = ais.getFormat();
                        DataLine.Info info = new DataLine.Info(SourceDataLine.class, format);
                        line = (SourceDataLine) AudioSystem.getLine(info);
                        line.open(format);
                        try {
                            FloatControl vol = (FloatControl) line.getControl(FloatControl.Type.MASTER_GAIN);
                            float dB = (float) (Math.log10(Math.max(0.0001, volume)) * 20.0);
                            vol.setValue(dB);
                        } catch (Exception ignored) {
                        }
                        line.start();
                        byte[] buffer = new byte[4096];
                        int n;
                        while (running && (n = ais.read(buffer)) != -1) {
                            line.write(buffer, 0, n);
                        }
                        line.drain();
                        line.close();
                    }
                } catch (Exception ignored) {
                }
                playing = false;
            }, "Music-Thread");
            thread.setDaemon(true);
            thread.start();
        }

        private static void playProcedural() {
            if (playing) {
                return;
            }
            playing = true;
            running = true;
            thread = new Thread(() -> {
                try {
                    AudioFormat fmt = new AudioFormat(44100, 16, 1, true, false);
                    DataLine.Info info = new DataLine.Info(SourceDataLine.class, fmt);
                    if (!AudioSystem.isLineSupported(info)) {
                        playing = false;
                        return;
                    }

                    byte[] melody = generateSoftMelody();
                    while (running) {
                        line = (SourceDataLine) AudioSystem.getLine(info);
                        line.open(fmt);
                        line.start();
                        int chunk = 4096;
                        for (int i = 0; i < melody.length && running; i += chunk) {
                            int len = Math.min(chunk, melody.length - i);
                            line.write(melody, i, len);
                        }
                        line.drain();
                        line.stop();
                        line.close();
                    }
                } catch (Exception ignored) {
                }
                playing = false;
            }, "Music-Procedural");
            thread.setDaemon(true);
            thread.start();
        }

        public static void stop() {
            running = false;
            if (line != null) {
                try {
                    line.stop();
                } catch (Exception ignored) {
                }
                try {
                    line.flush();
                } catch (Exception ignored) {
                }
            }
            if (thread != null) {
                thread.interrupt();
                thread = null;
            }
            playing = false;
            currentTrack = null;
        }

        public static boolean isPlaying() {
            return playing;
        }

        public static void setVolume(float v) {
            volume = Math.max(0f, Math.min(1f, v));
            if (line != null) {
                try {
                    FloatControl vol = (FloatControl) line.getControl(FloatControl.Type.MASTER_GAIN);
                    float dB = (float) (Math.log10(Math.max(0.0001, volume)) * 20.0);
                    vol.setValue(dB);
                } catch (Exception ignored) {
                }
            }
        }

        private static byte[] generateSoftMelody() {
            int sampleRate = 44100;
            double[][] chords = {
                {261.63, 329.63, 392.00, 493.88},
                {220.00, 261.63, 329.63, 392.00},
                {174.61, 220.00, 261.63, 329.63},
                {196.00, 246.94, 293.66, 349.23},
                {164.81, 196.00, 246.94, 293.66},
                {220.00, 261.63, 329.63, 392.00},
                {146.83, 174.61, 220.00, 261.63},
                {196.00, 246.94, 293.66, 349.23}
            };
            double[] melody = {
                523.25, 587.33, 659.25, 587.33,
                440.00, 523.25, 587.33, 523.25,
                349.23, 392.00, 440.00, 392.00,
                392.00, 440.00, 493.88, 440.00,
                329.63, 392.00, 493.88, 392.00,
                440.00, 523.25, 659.25, 523.25,
                293.66, 349.23, 440.00, 349.23,
                392.00, 440.00, 493.88, 523.25
            };

            double chordDuration = 4.0;
            int chordSamples = (int) (sampleRate * chordDuration);
            int totalSamples = chordSamples * chords.length;
            int melodyNoteSamples = chordSamples / 4;
            float[] mixBuf = new float[totalSamples];

            for (int c = 0; c < chords.length; c++) {
                int baseIdx = c * chordSamples;
                for (int n = 0; n < chords[c].length; n++) {
                    double freq = chords[c][n];
                    double noteAmp = 0.22 / (n + 1);
                    for (int i = 0; i < chordSamples; i++) {
                        double t = i / (double) sampleRate;
                        double attack = Math.min(1.0, i / (sampleRate * 0.4));
                        double release = Math.min(1.0, (chordSamples - i) / (sampleRate * 1.2));
                        double env = Math.pow(attack * release, 1.5);
                        double v = Math.sin(2 * Math.PI * freq * t)
                                + 0.3 * Math.sin(4 * Math.PI * freq * t);
                        mixBuf[baseIdx + i] += (float) (v * noteAmp * env);
                    }
                }
            }
            for (int m = 0; m < melody.length; m++) {
                double freq = melody[m];
                int chordIdx = m / 4;
                int noteIdx = m % 4;
                int baseIdx = chordIdx * chordSamples + noteIdx * melodyNoteSamples;
                for (int i = 0; i < melodyNoteSamples; i++) {
                    double t = i / (double) sampleRate;
                    double attack = Math.min(1.0, i / (sampleRate * 0.15));
                    double release = Math.min(1.0, (melodyNoteSamples - i) / (sampleRate * 0.5));
                    double env = Math.pow(attack * release, 1.2);
                    double v = Math.sin(2 * Math.PI * freq * t);
                    mixBuf[baseIdx + i] += (float) (v * 0.10 * env);
                }
            }
            byte[] out = new byte[totalSamples * 2];
            int fadeIn = (int) (sampleRate * 2.0);
            int fadeOut = (int) (sampleRate * 3.0);
            for (int i = 0; i < totalSamples; i++) {
                double sample = mixBuf[i];
                if (i < fadeIn) {
                    sample *= i / (double) fadeIn;
                }
                if (i > totalSamples - fadeOut) {
                    sample *= (totalSamples - i) / (double) fadeOut;
                }
                sample = Math.tanh(sample * 1.2) * volume;
                short s = (short) (sample * 32767 * 0.55);
                out[i * 2] = (byte) (s & 0xFF);
                out[i * 2 + 1] = (byte) ((s >> 8) & 0xFF);
            }
            return out;
        }
    }

    // ==================== MAIN ====================
    public static void main(String[] args) {
        SwingUtilities.invokeLater(() -> {
            JFrame frame = new JFrame(GAME_TITLE + " " + VERSION);
            try {
                frame.setIconImage(createMinecraftIcon());
            } catch (Exception ignored) {
            }
            TerraPixel game = new TerraPixel(frame);
            frame.add(game);
            frame.pack();
            frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
            frame.setLocationRelativeTo(null);
            frame.setResizable(true);
            frame.setVisible(true);
            game.requestFocusInWindow();
        });
    }
}
